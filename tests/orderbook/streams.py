# /// script
# requires-python = ">=3.10"
# ///
"""Write a random order book command stream, deterministic in the seed.
The generator runs each record through the reference book so that it can
pick ids and accounts of resting orders."""

import argparse
import random
import struct
import sys

sys.dont_write_bytecode = True
import reference as ob

WORD = ob.WORD
BIT63 = 1 << 63
MAX_QUANTITY = ob.MAX_QUANTITY
LIMIT, MARKET, CANCEL, REDUCE = ob.LIMIT, ob.MARKET, ob.CANCEL, ob.REDUCE
BUY, SELL = ob.BUY, ob.SELL
GTC, IOC, POST_ONLY = ob.GTC, ob.IOC, ob.POST_ONLY


class Stream:
    def __init__(self, seed):
        self.rng = random.Random(seed)
        self.book = ob.Book()
        self.words = []

    def put(self, record):
        self.words.extend(record)
        ob.step(self.book, record)

    def resting(self):
        return self.book.bids + self.book.asks

    def absent_id(self):
        """An id of no resting order: 0, an id not yet issued, or an
        earlier id that no longer rests."""
        rng = self.rng
        next_id = self.book.next_id
        r = rng.random()
        if r < 0.2 or next_id == 1:
            return rng.choice((0, next_id, next_id + rng.randint(1, 10)))
        live = {o.id for o in self.resting()}
        for _ in range(8):
            order_id = rng.randint(1, next_id - 1)
            if order_id not in live:
                return order_id
        return next_id

    def target(self, accounts, own=0.7, other=0.15):
        """An order id and an account for a cancel or reduce: a resting
        order and its account, a resting order and another account, or an
        id of no resting order.  Returns the order too, or None."""
        rng = self.rng
        resting = self.resting()
        r = rng.random()
        if resting and r < own + other:
            order = rng.choice(resting)
            if r < own:
                return order.id, order.account, order
            return order.id, rng.choice([a for a in accounts if a != order.account]), order
        return self.absent_id(), rng.choice(accounts), None


def new_quantity(rng, order):
    """A reduce quantity: mostly valid, sometimes equal to the remaining
    quantity, above it, or 0."""
    remaining = order.quantity if order else rng.randint(1, 10)
    r = rng.random()
    if r < 0.7 and remaining > 1:
        return rng.randint(1, remaining - 1)
    if r < 0.8:
        return remaining
    if r < 0.9:
        return remaining + rng.randint(1, 5)
    return 0


MIXED_ACCOUNTS = (1, 2, 3)


def mixed_record(s):
    rng = s.rng
    account = rng.choice(MIXED_ACCOUNTS)
    tag = rng.getrandbits(64)
    r = rng.random()
    if r < 0.5:
        tif = rng.choices((GTC, IOC, POST_ONLY), weights=(3, 1, 1))[0]
        return [LIMIT, rng.randrange(2), rng.randint(500, 510), rng.randint(1, 10),
                account, tag, tif]
    if r < 0.6:
        return [MARKET, rng.randrange(2), rng.randint(1, 15), account, tag, 0, 0]
    order_id, account, order = s.target(MIXED_ACCOUNTS)
    if r < 0.8:
        return [CANCEL, order_id, account, 0, 0, 0, 0]
    return [REDUCE, order_id, account, new_quantity(rng, order), 0, 0, 0]


def mixed(s, n):
    for _ in range(n):
        s.put(mixed_record(s))


def truncated(s, n):
    mixed(s, n)
    s.words.extend(mixed_record(s)[:s.rng.randint(1, 6)])


FULL_ACCOUNTS = tuple(range(1, 9))


def passive_price(s, side):
    """A price that does not cross the opposite side, or None."""
    if side == BUY:
        top = s.book.asks[0].price if s.book.asks else ob.MAX_PRICE + 1
        return s.rng.randint(1, top - 1) if top > 1 else None
    top = s.book.bids[0].price if s.book.bids else 0
    return s.rng.randint(top + 1, ob.MAX_PRICE) if top < ob.MAX_PRICE else None


def crossing_price(s, side):
    """A price that crosses the opposite side's first order, or None."""
    opposite = s.book.side(1 - side)
    if not opposite:
        return None
    best = opposite[0].price
    if side == BUY:
        return min(ob.MAX_PRICE, best + s.rng.randint(0, 2))
    return max(1, best - s.rng.randint(0, 2))


def full_record(s):
    rng = s.rng
    side = rng.randrange(2)
    account = rng.choice(FULL_ACCOUNTS)
    tag = rng.getrandbits(64)
    r = rng.random()
    if r < 0.45:
        tif = POST_ONLY if r < 0.1 else GTC
        if r < 0.02:
            price = crossing_price(s, side)
        else:
            price = passive_price(s, side)
        if price is None:
            price = rng.randint(1, ob.MAX_PRICE)
        return [LIMIT, side, price, rng.randint(1, 100), account, tag, tif]
    if r < 0.62:
        price = crossing_price(s, side) or rng.randint(1, ob.MAX_PRICE)
        opposite = s.book.side(1 - side)
        quantity = rng.randint(1, 2 * opposite[0].quantity + 1) if opposite else 10
        tif = IOC if r < 0.56 else GTC
        return [LIMIT, side, price, quantity, account, tag, tif]
    if r < 0.66:
        return [MARKET, side, rng.randint(1, 30), account, tag, 0, 0]
    order_id, account, order = s.target(FULL_ACCOUNTS, own=0.9, other=0.05)
    if r < 0.92:
        return [CANCEL, order_id, account, 0, 0, 0, 0]
    return [REDUCE, order_id, account, new_quantity(rng, order), 0, 0, 0]


def full(s, n):
    rng = s.rng
    first = min(n, ob.CAPACITY)
    for _ in range(first):
        side = rng.randrange(2)
        price = rng.randint(1, 511) if side == BUY else rng.randint(513, ob.MAX_PRICE)
        s.put([LIMIT, side, price, rng.randint(1, 100), rng.choice(FULL_ACCOUNTS),
               rng.getrandbits(64), GTC])
    for _ in range(n - first):
        s.put(full_record(s))


EDGE_PRICES = (0, 1, 1023, 1024, WORD)
EDGE_QUANTITIES = (0, 1, MAX_QUANTITY, MAX_QUANTITY + 1, WORD)
EDGE_TAGS = (0, 1, MAX_QUANTITY, 1 << 32, (1 << 32) + 1, WORD)
EDGE_IDS = (0, MAX_QUANTITY, 1 << 32, (1 << 32) + 1, WORD)
EDGE_ACCOUNTS = (0, BIT63, 5, 5 | BIT63, WORD >> 1, WORD)
EDGE_FILLER = (1, MAX_QUANTITY, 1 << 32, BIT63, WORD)


def edge_side(rng):
    return rng.choice((BUY, SELL, BUY, SELL, BUY, SELL, 2, WORD))


def edge_word(rng, edges, low, high):
    return rng.choice(edges) if rng.random() < 0.5 else rng.randint(low, high)


def unused(rng, k):
    """k unused words: zero or nonzero edge words."""
    if rng.random() < 0.5:
        return [0] * k
    return [rng.choice(EDGE_FILLER) for _ in range(k)]


def edges_record(s):
    rng = s.rng
    account = rng.choice(EDGE_ACCOUNTS)
    tag = rng.choice(EDGE_TAGS) if rng.random() < 0.7 else rng.getrandbits(64)
    r = rng.random()
    if r < 0.05:
        if s.book.asks and rng.random() < 0.5:
            side, price = BUY, rng.choice((1024, WORD))
        elif s.book.bids:
            side, price = SELL, 0
        else:
            side, price = BUY, rng.choice((1024, WORD))
        return [LIMIT, side, price, rng.randint(1, 10), account, tag, POST_ONLY]
    if r < 0.45:
        tif = rng.choice((GTC, IOC, POST_ONLY, GTC, IOC, POST_ONLY, 3, WORD))
        return [LIMIT, edge_side(rng), edge_word(rng, EDGE_PRICES, 1, 1023),
                edge_word(rng, EDGE_QUANTITIES, 1, 10), account, tag, tif]
    if r < 0.6:
        return [MARKET, edge_side(rng), edge_word(rng, EDGE_QUANTITIES, 1, 10),
                account, tag] + unused(rng, 2)
    if r < 0.85:
        resting = s.resting()
        if resting and rng.random() < 0.6:
            order = rng.choice(resting)
            order_id = order.id
            account = rng.choice((order.account, order.account, order.account ^ BIT63))
        else:
            order = None
            order_id = rng.choice(EDGE_IDS + (s.book.next_id,))
        if r < 0.7:
            return [CANCEL, order_id, account] + unused(rng, 4)
        if order and rng.random() < 0.5:
            q = order.quantity
            quantity = rng.choice((1, q - 1, q, q + 1))
        else:
            quantity = rng.choice(EDGE_QUANTITIES)
        return [REDUCE, order_id, account, quantity] + unused(rng, 3)
    return [rng.choice((0, 5, WORD))] + [rng.getrandbits(64) | 1 for _ in range(6)]


def edges(s, n):
    for _ in range(n):
        s.put(edges_record(s))


PROFILES = {"mixed": mixed, "full": full, "edges": edges, "truncated": truncated}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, required=True)
    parser.add_argument("--commands", type=int, required=True,
                        help="number of seven-word records")
    parser.add_argument("--out", required=True)
    parser.add_argument("--profile", choices=PROFILES, default="mixed")
    args = parser.parse_args()
    if args.commands < 0:
        parser.error("--commands must be at least 0")
    s = Stream(args.seed)
    PROFILES[args.profile](s, args.commands)
    with open(args.out, "wb") as f:
        f.write(struct.pack(f"<{len(s.words)}Q", *s.words))


if __name__ == "__main__":
    main()
