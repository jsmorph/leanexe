# /// script
# requires-python = ">=3.10"
# ///
"""Run an order book command stream from the empty book and print the
events, the next id, the resting orders, and the top of book."""

import argparse
import bisect
import struct
import sys

WORD = (1 << 64) - 1
MAX_PRICE = 1023
MAX_QUANTITY = (1 << 32) - 1
CAPACITY = 4096

LIMIT, MARKET, CANCEL, REDUCE = 1, 2, 3, 4
BUY, SELL = 0, 1
GTC, IOC, POST_ONLY = 0, 1, 2

ACCEPTED, REJECTED, TRADE, CANCELLED, REDUCED = 1, 2, 3, 4, 5

NOT_SEVEN_WORDS = 1
UNKNOWN_KIND = 2
BAD_SIDE = 3
BAD_TIME_IN_FORCE = 4
BAD_PRICE = 5
BAD_QUANTITY = 6
NO_ORDER = 7
OTHER_ACCOUNT = 8
WOULD_CROSS = 9
NOT_BELOW = 10

REQUESTED = 1
IOC_REMAINDER = 2
SELF_TRADE = 3
BOOK_FULL = 4


class Order:
    __slots__ = ("id", "account", "price", "quantity")

    def __init__(self, id, account, price, quantity):
        self.id = id
        self.account = account
        self.price = price
        self.quantity = quantity


class Book:
    """Each side lists its resting orders in priority order, best first."""

    def __init__(self):
        self.bids = []
        self.asks = []
        self.next_id = 1

    def side(self, side):
        return self.bids if side == BUY else self.asks

    def size(self):
        return len(self.bids) + len(self.asks)


def event(*words):
    return words + (0,) * (7 - len(words))


def acceptable(side, price, resting_price):
    """Whether an incoming order on `side` at `price` accepts a resting
    order's price.  A market order has price None."""
    if price is None:
        return True
    return resting_price <= price if side == BUY else resting_price >= price


def valid_quantity(quantity):
    return 1 <= quantity <= MAX_QUANTITY


def step(book, record):
    """Apply one record to the book and return its events."""
    if len(record) != 7:
        return [event(REJECTED, 0, 0, NOT_SEVEN_WORDS)]
    kind = record[0]
    if kind == LIMIT:
        return limit(book, *record[1:7])
    if kind == MARKET:
        return market(book, *record[1:5])
    if kind == CANCEL:
        return cancel(book, *record[1:3])
    if kind == REDUCE:
        return reduce(book, *record[1:4])
    return [event(REJECTED, kind, 0, UNKNOWN_KIND)]


def limit(book, side, price, quantity, account, tag, tif):
    if side > SELL:
        reason = BAD_SIDE
    elif tif > POST_ONLY:
        reason = BAD_TIME_IN_FORCE
    elif not 1 <= price <= MAX_PRICE:
        reason = BAD_PRICE
    elif not valid_quantity(quantity):
        reason = BAD_QUANTITY
    elif tif == POST_ONLY and crosses(book, side, price):
        reason = WOULD_CROSS
    else:
        return accept(book, side, price, quantity, account, tag, tif)
    return [event(REJECTED, LIMIT, tag, reason)]


def market(book, side, quantity, account, tag):
    if side > SELL:
        reason = BAD_SIDE
    elif not valid_quantity(quantity):
        reason = BAD_QUANTITY
    else:
        return accept(book, side, None, quantity, account, tag, IOC)
    return [event(REJECTED, MARKET, tag, reason)]


def crosses(book, side, price):
    opposite = book.side(1 - side)
    return bool(opposite) and acceptable(side, price, opposite[0].price)


def accept(book, side, price, quantity, account, tag, tif):
    """Accept an order with valid fields, match it, and handle its remainder.
    A market order has price None and the remainder handling of IOC.  A
    post-only order reaches here only when it does not cross, so the
    matching loop makes no trade for it."""
    order_id = book.next_id
    book.next_id = (order_id + 1) & WORD
    events = [event(ACCEPTED, order_id, tag)]
    opposite = book.side(1 - side)
    remaining = quantity
    self_trade = False
    while remaining and opposite and acceptable(side, price, opposite[0].price):
        maker = opposite[0]
        if maker.account == account:
            self_trade = True
            break
        traded = min(remaining, maker.quantity)
        remaining -= traded
        maker.quantity -= traded
        events.append(event(TRADE, maker.id, order_id, maker.price, traded,
                            maker.account, maker.quantity))
        if maker.quantity == 0:
            opposite.pop(0)
    if remaining:
        if self_trade:
            reason = SELF_TRADE
        elif tif == IOC:
            reason = IOC_REMAINDER
        elif book.size() < CAPACITY:
            rest(book, side, Order(order_id, account, price, remaining))
            return events
        else:
            reason = BOOK_FULL
        events.append(event(CANCELLED, order_id, remaining, reason))
    return events


def rest(book, side, order):
    """Insert the order behind every resting order at its price or better."""
    orders = book.side(side)
    if side == BUY:
        i = bisect.bisect_right(orders, -order.price, key=lambda o: -o.price)
    else:
        i = bisect.bisect_right(orders, order.price, key=lambda o: o.price)
    orders.insert(i, order)


def find(book, order_id):
    for orders in (book.bids, book.asks):
        for i, order in enumerate(orders):
            if order.id == order_id:
                return orders, i
    return None, None


def cancel(book, order_id, account):
    orders, i = find(book, order_id)
    if orders is None:
        reason = NO_ORDER
    elif orders[i].account != account:
        reason = OTHER_ACCOUNT
    else:
        order = orders.pop(i)
        return [event(CANCELLED, order_id, order.quantity, REQUESTED)]
    return [event(REJECTED, CANCEL, order_id, reason)]


def reduce(book, order_id, account, quantity):
    orders, i = find(book, order_id)
    if orders is None:
        reason = NO_ORDER
    elif orders[i].account != account:
        reason = OTHER_ACCOUNT
    elif not valid_quantity(quantity):
        reason = BAD_QUANTITY
    elif quantity >= orders[i].quantity:
        reason = NOT_BELOW
    else:
        orders[i].quantity = quantity
        return [event(REDUCED, order_id, quantity)]
    return [event(REJECTED, REDUCE, order_id, reason)]


def best(orders):
    """Best price and total remaining quantity at it, or 0 and 0."""
    if not orders:
        return 0, 0
    price = orders[0].price
    return price, sum(o.quantity for o in orders if o.price == price)


def run(words):
    """Run a word sequence from the empty book; return the output lines."""
    book = Book()
    lines = []
    for i in range(0, len(words), 7):
        for e in step(book, words[i:i + 7]):
            lines.append("event " + " ".join(map(str, e)))
    lines.append(f"next {book.next_id}")
    for o in book.bids:
        lines.append(f"bid {o.id} {o.account} {o.price} {o.quantity}")
    for o in book.asks:
        lines.append(f"ask {o.id} {o.account} {o.price} {o.quantity}")
    bid_price, bid_quantity = best(book.bids)
    ask_price, ask_quantity = best(book.asks)
    lines.append(f"top {bid_price} {bid_quantity} {ask_price} {ask_quantity}")
    return lines


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stream", help="file of little-endian 64-bit words")
    args = parser.parse_args()
    with open(args.stream, "rb") as f:
        data = f.read()
    if len(data) % 8:
        print(f"{args.stream}: length {len(data)} bytes is not a multiple of 8",
              file=sys.stderr)
        sys.exit(2)
    words = struct.unpack(f"<{len(data) // 8}Q", data)
    sys.stdout.write("\n".join(run(words)) + "\n")


if __name__ == "__main__":
    main()
