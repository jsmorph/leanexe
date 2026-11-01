# /// script
# requires-python = ">=3.10"
# ///
"""Write the hand-written edge streams into the directory OUT, one file of
little-endian 64-bit words per case."""

import argparse
import struct
from pathlib import Path

WORD = (1 << 64) - 1
BIT63 = 1 << 63
MAX_QUANTITY = (1 << 32) - 1

BUY, SELL = 0, 1
GTC, IOC, POST_ONLY = 0, 1, 2


def limit(side, price, quantity, account, tag, tif=GTC):
    return [1, side, price, quantity, account, tag, tif]


def market(side, quantity, account, tag):
    return [2, side, quantity, account, tag, 0, 0]


def cancel(order_id, account):
    return [3, order_id, account, 0, 0, 0, 0]


def reduce(order_id, account, quantity):
    return [4, order_id, account, quantity, 0, 0, 0]


def fill():
    """4,096 non-crossing GTC orders.  Ids 1 to 4,095 alternate a bid at
    100 + k % 300 from account 1000 + k % 4 (odd ids) and an ask at
    600 + k % 300 from account 2000 + k % 4 (even ids), each of quantity 10,
    where k is half the id rounded down.  Id 4,096 is the only ask at 550,
    of quantity 4 from account 3000."""
    records = []
    for i in range(4095):
        k = i // 2
        if i % 2 == 0:
            records.append(limit(BUY, 100 + k % 300, 10, 1000 + k % 4, i + 1))
        else:
            records.append(limit(SELL, 600 + k % 300, 10, 2000 + k % 4, i + 1))
    records.append(limit(SELL, 550, 4, 3000, 4096))
    return records


CASES = {
    "empty": [],
    "three-words": [[1, 0, 100]],
    "short-final-record": [
        limit(BUY, 100, 1, 1, 1),
        [3, 1, 1, 0],
    ],
    "market-buy-two-ask-prices": [
        limit(SELL, 100, 5, 11, 1),
        limit(SELL, 101, 5, 12, 2),
        limit(SELL, 102, 5, 13, 3),
        market(BUY, 8, 21, 4),
    ],
    "market-empty-side": [
        market(BUY, 5, 1, 10),
        market(SELL, MAX_QUANTITY, 1, 11),
    ],
    "market-self-trade": [
        limit(SELL, 100, 3, 11, 1),
        market(BUY, 5, 11, 2),
    ],
    "ioc-partial-and-unmatched": [
        limit(SELL, 100, 3, 11, 1),
        limit(BUY, 100, 5, 22, 2, IOC),
        limit(BUY, 100, 4, 22, 3, IOC),
    ],
    "gtc-partial-fill-rests": [
        limit(SELL, 100, 3, 1, 1),
        limit(SELL, 102, 3, 2, 2),
        limit(BUY, 101, 5, 3, 3),
    ],
    "price-time-priority": [
        limit(BUY, 100, 1, 1, 1),
        limit(BUY, 101, 2, 2, 2),
        limit(BUY, 100, 3, 3, 3),
        limit(BUY, 101, 4, 4, 4),
        limit(BUY, 99, 5, 5, 5),
        limit(SELL, 100, 8, 6, 6),
        limit(SELL, 105, 1, 7, 7),
        limit(SELL, 104, 1, 8, 8),
        limit(SELL, 105, 1, 9, 9),
    ],
    "self-trade-stop-behind-trade": [
        limit(SELL, 100, 3, 11, 1),
        limit(SELL, 100, 4, 22, 2),
        limit(SELL, 101, 5, 33, 3),
        limit(BUY, 101, 10, 22, 4),
    ],
    "accounts-differ-in-bit-63": [
        limit(SELL, 100, 5, 7, 1),
        limit(BUY, 100, 2, 7 | BIT63, 2),
        limit(BUY, 100, 1, 7, 3),
        limit(SELL, 100, 1, BIT63, 4),
        market(BUY, 4, 0, 5),
    ],
    "post-only-crossing-and-accepted": [
        limit(SELL, 100, 5, 11, 1),
        limit(BUY, 100, 2, 22, 2, POST_ONLY),
        limit(BUY, 100, 2, 11, 3, POST_ONLY),
        limit(BUY, 99, 2, 22, 4, POST_ONLY),
        limit(SELL, 99, 1, 33, 5, POST_ONLY),
        limit(SELL, 100, 1, 33, 6, POST_ONLY),
    ],
    "post-only-bad-fields-would-cross": [
        limit(SELL, 100, 5, 11, 1),
        limit(BUY, 90, 5, 12, 2),
        limit(BUY, 1024, 1, 22, 3, POST_ONLY),
        limit(BUY, WORD, 1, 22, 4, POST_ONLY),
        limit(SELL, 0, 1, 22, 5, POST_ONLY),
        limit(BUY, 100, 0, 22, 6, POST_ONLY),
        limit(BUY, 100, 1 << 32, 22, 7, POST_ONLY),
    ],
    "reduce-to-one-and-to-same": [
        limit(BUY, 50, 10, 11, 1),
        limit(BUY, 50, 3, 12, 2),
        reduce(1, 11, 1),
        reduce(2, 12, 3),
        reduce(1, 11, 1),
        reduce(1, 11, 0),
        reduce(1, 11, 1 << 32),
        reduce(2, 11, 1),
        reduce(9, 11, 1),
        limit(SELL, 50, 2, 33, 3),
    ],
    "cancel-wrong-account": [
        limit(SELL, 200, 5, 11, 1),
        cancel(1, 12),
        cancel(1, 11 | BIT63),
        cancel(2, 11),
        cancel(1, 11),
        cancel(1, 11),
    ],
    "rejection-reasons": [
        [1, 2, 100, 1, 1, 10, GTC],
        [1, 2, 0, 0, 1, 11, 3],
        [1, BUY, 0, 0, 1, 12, 3],
        [1, BUY, 0, 0, 1, 13, GTC],
        [1, SELL, 1024, 1, 1, 14, IOC],
        [1, BUY, 1, 0, 1, 15, GTC],
        [1, BUY, 1023, 1 << 32, 1, 16, GTC],
        [1, WORD, 1, 1, 1, 17, WORD],
        [1, BUY, 1, 1, 1, 18, WORD],
        [2, 2, 5, 1, 19, 0, 0],
        [2, BUY, 0, 1, 20, 0, 0],
        [2, SELL, WORD, 1, 21, 0, 0],
        [0, 1, 2, 3, 4, 5, 6],
        [5, 1, 2, 3, 4, 5, 6],
        [WORD, WORD, WORD, WORD, WORD, WORD, WORD],
        cancel(1, 1),
        reduce(1 << 32, 1, 1),
        cancel(WORD, 1),
        cancel(0, 0),
    ],
    "unused-words-ignored": [
        limit(SELL, 100, 5, 11, 1),
        [2, BUY, 2, 22, 2, WORD, WORD],
        [4, 1, 11, 2, WORD, 7, 8],
        [3, 1, 11, 9, 9, 9, 9],
    ],
    "maximum-quantities-top-total": [
        limit(SELL, 1023, MAX_QUANTITY, 1, 1),
        limit(SELL, 1023, MAX_QUANTITY, 2, 2),
        limit(SELL, 1023, MAX_QUANTITY, 3, 3),
        limit(BUY, 1, MAX_QUANTITY, 4, 4),
        limit(BUY, 1, MAX_QUANTITY, 5, 5),
        market(BUY, MAX_QUANTITY, 9, 6),
    ],
    "book-full-gtc-cancelled-book-full": fill() + [
        limit(BUY, 500, 7, 1, 5001),
        limit(SELL, 500, 7, 1, 5002),
        cancel(1, 1000),
        limit(BUY, 500, 7, 1, 5003),
        limit(BUY, 450, 3, 1, 5004),
    ],
    "book-full-maker-exhausted-remainder-rests": fill() + [
        limit(BUY, 550, 9, 1, 6001),
        limit(BUY, 550, 2, 1, 6002),
    ],
    "book-full-self-trade-precedence": fill() + [
        limit(BUY, 550, 9, 3000, 7001),
        limit(BUY, 600, 20, 2000, 7002),
    ],
    "book-full-ioc-and-post-only": fill() + [
        limit(BUY, 500, 3, 1, 8001, IOC),
        limit(BUY, 500, 3, 1, 8002, POST_ONLY),
        limit(BUY, 550, 3, 1, 8003, POST_ONLY),
        market(SELL, 5, 1, 8004),
    ],
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("out", help="directory for the streams, created if absent")
    args = parser.parse_args()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    for name, records in CASES.items():
        words = [w for record in records for w in record]
        (out / f"{name}.bin").write_bytes(struct.pack(f"<{len(words)}Q", *words))


if __name__ == "__main__":
    main()
