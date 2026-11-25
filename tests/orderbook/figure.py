# /// script
# requires-python = ">=3.12"
# dependencies = ["matplotlib==3.11.2"]
# ///
"""Draws one session of the order book from the program's output: the best bid and the best ask
after each command, with the trades, and the depth of the final book at each price.

STREAM is the command stream, as little-endian 64-bit words, and OUTPUT is the program's output on
it from the empty book with next id 1, as `orderbook-compare stream` prints it in the format of
reference.py.  The script rebuilds the book from OUTPUT's events, with the side, price, quantity,
and account of each accepted order from its command: a trade lowers its maker's quantity and
removes an exhausted maker, a cancellation removes its order, a reduction sets its order's
quantity, and the remainder of an accepted limit order that no cancellation ends rests behind the
orders at its price.  It requires each event to agree with the rebuilt book, the events to end
with the last command, and the rebuilt book's next id, orders, and top of book to equal OUTPUT's.
The best prices come from the rebuilt book, and the trades and the depth from OUTPUT.  The format
of OUT, SVG or PNG, follows its extension.  The exit status is 0 when the figure is drawn, 1 when
an event disagrees with the rebuilt book or the rebuilt book differs from OUTPUT's final book, and
2 for a usage error.

Usage: uv run tests/orderbook/figure.py STREAM OUTPUT OUT
"""

import os
import struct
import sys

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
from matplotlib.ticker import MaxNLocator

matplotlib.rcParams["svg.hashsalt"] = "orderbook-figure"

INK, MUTED, GRID = "#111111", "#555555", "#dddddd"
BID, ASK = "#0072b2", "#d55e00"

LIMIT, MARKET, CANCEL, REDUCE = 1, 2, 3, 4
BUY, SELL = 0, 1
ACCEPTED, REJECTED, TRADE, CANCELLED, REDUCED = 1, 2, 3, 4, 5
REQUESTED = 1

W, H = 7.3, 4.3
LEFT, SPLIT, GAP, RIGHT = 0.55, 5.35, 0.3, 0.45
TOP, BOTTOM = 0.95, 0.5


class Difference(Exception):
    pass


def records(path):
    with open(path, "rb") as f:
        data = f.read()
    if len(data) % 8:
        raise ValueError(f"{path}: length {len(data)} bytes is not a multiple of 8")
    words = struct.unpack(f"<{len(data) // 8}Q", data)
    return [words[i:i + 7] for i in range(0, len(words), 7)]


def output(path):
    """OUTPUT's events, next id, resting orders by side, and top of book."""
    out = {"events": [], "next": None, "book": {BUY: [], SELL: []}, "top": None}
    with open(path, encoding="utf-8") as f:
        for line in f:
            word, *fields = line.split()
            values = [int(v) for v in fields]
            if word == "event":
                out["events"].append(values)
            elif word == "next":
                out["next"] = values[0]
            elif word in ("bid", "ask"):
                out["book"][BUY if word == "bid" else SELL].append(values)
            elif word == "top":
                out["top"] = values
            else:
                raise ValueError(f"{path}: unknown line {line.strip()}")
    return out


def best(orders):
    if not orders:
        return 0, 0
    price = orders[0][2]
    return price, sum(o[3] for o in orders if o[2] == price)


def find(book, k, order_id):
    for side, orders in book.items():
        for order in orders:
            if order[0] == order_id:
                return side, order
    raise Difference(f"command {k}: no resting order {order_id}")


def rest(orders, side, order):
    """Inserts the order behind every order at its price or a better one."""
    i = 0
    while i < len(orders) and (orders[i][2] >= order[2] if side == BUY else
                               orders[i][2] <= order[2]):
        i += 1
    orders.insert(i, order)


def rebuild(commands, out):
    """The best bid and ask after each command and the trades (command, price, quantity, taker's
    side), from the events; raises Difference when an event or the final book disagrees.  Each
    side of the book lists its orders [id, account, price, quantity] in priority order."""
    book = {BUY: [], SELL: []}
    events = out["events"]
    e = 0
    next_id = 1
    tops, trades = [], []
    for k, command in enumerate(commands, 1):
        if e == len(events):
            raise Difference(f"command {k}: the events end")
        event = events[e]
        e += 1
        kind = event[0]
        if kind == ACCEPTED:
            if len(command) != 7 or command[0] not in (LIMIT, MARKET):
                raise Difference(f"command {k}: accepted, but it is no limit or market order")
            if command[0] == LIMIT:
                _, side, price, quantity, account, tag, _ = command
            else:
                _, side, quantity, account, tag, _, _ = command
                price = None
            order_id = event[1]
            if order_id != next_id or event[2] != tag:
                raise Difference(f"command {k}: accepted event {event} for id {next_id} and tag "
                                 f"{tag}")
            next_id += 1
            remaining = quantity
            while e < len(events) and events[e][0] == TRADE and events[e][2] == order_id:
                _, maker_id, _, at, traded, maker_account, left = events[e]
                e += 1
                maker_side, maker = find(book, k, maker_id)
                if (maker_side == side or maker[2] != at or maker[1] != maker_account
                        or maker[3] - traded != left or not 0 < traded <= remaining):
                    raise Difference(f"command {k}: trade {events[e - 1]} disagrees with the "
                                     f"maker {maker} on side {maker_side}")
                maker[3] = left
                if left == 0:
                    book[maker_side].remove(maker)
                remaining -= traded
                trades.append((k, at, traded, side))
            ended = e < len(events) and events[e][0] == CANCELLED and events[e][1] == order_id \
                and events[e][3] != REQUESTED
            if ended:
                if events[e][2] != remaining or remaining == 0:
                    raise Difference(f"command {k}: cancellation {events[e]} of a remainder of "
                                     f"{remaining}")
                e += 1
            elif remaining and price is None:
                raise Difference(f"command {k}: a market order's remainder of {remaining} rests")
            elif remaining:
                rest(book[side], side, [order_id, account, price, remaining])
        elif kind == CANCELLED:
            if len(command) != 7 or command[0] != CANCEL or event[3] != REQUESTED:
                raise Difference(f"command {k}: cancellation {event} for the command {command}")
            side, order = find(book, k, event[1])
            if command[1:3] != (order[0], order[1]) or event[2] != order[3]:
                raise Difference(f"command {k}: cancellation {event} of the order {order}")
            book[side].remove(order)
        elif kind == REDUCED:
            if len(command) != 7 or command[0] != REDUCE:
                raise Difference(f"command {k}: reduction {event} for the command {command}")
            side, order = find(book, k, event[1])
            if command[1:4] != (order[0], order[1], event[2]) or not 0 < event[2] < order[3]:
                raise Difference(f"command {k}: reduction {event} of the order {order}")
            order[3] = event[2]
        elif kind != REJECTED:
            raise Difference(f"command {k}: event {event} begins no command's events")
        bid, ask = book[BUY], book[SELL]
        tops.append((bid[0][2] if bid else None, ask[0][2] if ask else None))
    if e != len(events):
        raise Difference(f"{len(events) - e} events follow the last command's")
    if next_id != out["next"]:
        raise Difference(f"rebuilt next id {next_id}, output's {out['next']}")
    for side, name in ((BUY, "bids"), (SELL, "asks")):
        if book[side] != out["book"][side]:
            raise Difference(f"rebuilt {name} {book[side]}, output's {out['book'][side]}")
    top = [*best(book[BUY]), *best(book[SELL])]
    if top != out["top"]:
        raise Difference(f"rebuilt top {top}, output's {out['top']}")
    return tops, trades


def draw(name, commands, out, tops, trades, path):
    fig = plt.figure(figsize=(W, H))
    plot_h = H - TOP - BOTTOM
    left = fig.add_axes([LEFT / W, BOTTOM / H, (SPLIT - LEFT) / W, plot_h / H])
    depth = fig.add_axes([(SPLIT + GAP) / W, BOTTOM / H, (W - SPLIT - GAP - RIGHT) / W,
                          plot_h / H], sharey=left)
    n = len(commands)
    xs = range(1, n + 1)
    for k, color in enumerate((BID, ASK)):
        ys = [float("nan") if t[k] is None else t[k] for t in tops]
        left.step(xs, ys, where="post", color=color, linewidth=1.1, zorder=2)
    for side, marker in ((BUY, "^"), (SELL, "v")):
        shown = [(k, p) for k, p, _, s in trades if s == side]
        left.scatter([k for k, _ in shown], [p for _, p in shown], marker=marker, s=13,
                     facecolor=INK, edgecolor="white", linewidth=0.3, zorder=3)
    levels = {}
    for side in (BUY, SELL):
        for _, _, price, quantity in out["book"][side]:
            levels[(side, price)] = levels.get((side, price), 0) + quantity
    most = max(levels.values(), default=1)
    for (side, price), quantity in sorted(levels.items()):
        depth.barh(price, quantity, height=0.62, color=BID if side == BUY else ASK, linewidth=0)
        depth.text(quantity + most * 0.04, price, f"{quantity}", va="center", fontsize=8,
                   color=INK)
    prices = [p for t in tops for p in t if p is not None] + [p for _, p, _, _ in trades] + \
        [price for _, price in levels]
    left.set_ylim(min(prices) - 0.7, max(prices) + 0.7)
    left.set_yticks(range(min(prices), max(prices) + 1))
    left.set_xlim(0, n + 1)
    depth.set_xlim(0, most * 1.35)
    for ax in (left, depth):
        ax.grid(axis="y", color=GRID, linewidth=0.6)
        ax.set_axisbelow(True)
        for spine in ("top", "right"):
            ax.spines[spine].set_visible(False)
        ax.tick_params(colors=INK, labelsize=8.5)
    depth.tick_params(axis="y", labelleft=False, length=0)
    depth.xaxis.set_major_locator(MaxNLocator(3, integer=True))
    left.set_xlabel("Command", fontsize=9, color=INK)
    left.set_ylabel("Price (ticks)", fontsize=9, color=INK)
    depth.set_xlabel("Quantity", fontsize=9, color=INK)
    depth.set_title("Final book", fontsize=9, color=INK, loc="left", pad=4)
    accepted = sum(1 for event in out["events"] if event[0] == ACCEPTED)
    bought = sum(1 for trade in trades if trade[3] == BUY)
    fig.text(LEFT / W, 1 - 0.24 / H,
             f"{name}: {n:,} commands, {accepted:,} accepted orders, {len(trades):,} trades",
             fontsize=9, color=MUTED, va="baseline")
    handles = [Line2D([], [], color=BID, linewidth=1.1, label="Best bid"),
               Line2D([], [], color=ASK, linewidth=1.1, label="Best ask"),
               Line2D([], [], color=INK, marker="^", linestyle="none", markersize=4.5,
                      label=f"Trade, a buy order takes an ask ({bought:,})"),
               Line2D([], [], color=INK, marker="v", linestyle="none", markersize=4.5,
                      label=f"Trade, a sell order takes a bid ({len(trades) - bought:,})")]
    fig.legend(handles=handles, loc="upper left", bbox_to_anchor=(LEFT / W - 0.01, 1 - 0.3 / H),
               ncol=2, frameon=False, fontsize=8.5, handlelength=1.6, columnspacing=1.2)
    fig.savefig(path, metadata={"Date": None} if path.endswith(".svg") else None, dpi=150)


def main():
    if len(sys.argv) != 4:
        print(__doc__.strip().splitlines()[-1], file=sys.stderr)
        return 2
    stream, result, path = sys.argv[1:]
    commands, out = records(stream), output(result)
    try:
        tops, trades = rebuild(commands, out)
    except Difference as d:
        print(f"figure.py: {result}: {d}", file=sys.stderr)
        return 1
    name = os.path.splitext(os.path.basename(stream))[0]
    draw(name, commands, out, tops, trades, path)
    return 0


if __name__ == "__main__":
    sys.exit(main())
