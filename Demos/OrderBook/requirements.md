# Order book requirements

The order book matches orders for one instrument by price-time priority.  It is a deterministic function from a book and one command to a new book and a list of events.  The host sequences and authenticates commands, keeps the command log, and learns each order's id from the events.

## Limits

Prices are integer ticks from 1 to 1,023, and quantities are integers from 1 to 2^32 − 1.  The book holds at most 4,096 resting orders.  Accounts and client tags are arbitrary 64-bit words.  The book compares accounts for equality and copies accounts and client tags into events.

## Orders and priority

Each accepted order receives an id: the first accepted order has id 1, and each later accepted order has the id of the previous one plus 1, modulo 2^64.  A rejected command consumes no id.  The requirements cover streams of fewer than 2^64 − 1 accepted orders, in which the next id never wraps to 0 and the ids of resting orders are distinct.  A resting order has an id, an account, a side, a price, and a remaining quantity of at least 1.  On each side, resting orders are in priority order: an order at a better price comes first, where a better price is a higher one for bids and a lower one for asks, and among orders at the same price the order accepted earlier comes first.

## Commands

| Command | Fields | Meaning |
|---|---|---|
| `limit` | side, price, quantity, account, client tag, time in force | Buy or sell up to the quantity at the price or better |
| `market` | side, quantity, account, client tag | Buy or sell up to the quantity at any price |
| `cancel` | order id, account | Remove a resting order |
| `reduce` | order id, account, new quantity | Lower a resting order's remaining quantity |

The side is buy or sell, and the time in force of a limit order is GTC, IOC, or post-only.

## Matching

A `limit` order with GTC or IOC, or a `market` order, is accepted when its fields are valid, and an `accepted` event with its id and client tag comes first among its events.  It then matches against the opposite side, starting from that side's first order in priority order.  A buy order accepts an ask whose price is at most the buy's price, a sell order accepts a bid whose price is at least the sell's price, and a `market` order accepts every price.  While the incoming order has a remaining quantity and the opposite side's first order has an acceptable price, the following happens:

1. If the first opposite order has the incoming order's account, matching stops for self-trade prevention.  That resting order stays unchanged.
2. Otherwise a trade takes place at the resting order's price, for the smaller of the two remaining quantities.  The trade event names the resting order (the maker), the incoming order (the taker), the price, the quantity, the maker's account, and the maker's remaining quantity after the trade.
3. Both remaining quantities decrease by the traded quantity, and a maker whose remaining quantity reaches 0 leaves the book.

When matching ends with a remaining quantity, the remainder is handled as follows:

| Case | Result |
|---|---|
| Matching stopped for self-trade prevention | Remainder cancelled, reason self-trade |
| IOC limit order or `market` order | Remainder cancelled, reason IOC |
| GTC limit order, with fewer than 4,096 resting orders | Remainder rests at the order's price, behind every resting order at that price, with no further event |
| GTC limit order, with 4,096 resting orders | Remainder cancelled, reason book full |

When more than one row applies, the first row that applies decides, so self-trade prevention takes precedence over IOC and over a full book.  The count of resting orders is taken after matching, when the makers that the order exhausted have left the book.  A `market` order whose opposite side is empty is accepted and has its whole quantity cancelled with reason IOC.

A post-only `limit` order is rejected, with no id, when the opposite side's first order has an acceptable price.  Otherwise it is accepted, with its `accepted` event first, makes no trade, and rests as a GTC order would, or is cancelled with reason book full when the book holds 4,096 resting orders.

## Cancel and reduce

`cancel` removes the resting order with the given id when its account is the command's account, with a `cancelled` event that gives its remaining quantity and the reason requested.  `reduce` sets the remaining quantity of such an order to the new quantity, with a `reduced` event, and the order keeps its place in priority order.  The new quantity must be at least 1 and below the order's remaining quantity.

## Rejections

A command that fails a check is rejected with one `rejected` event, which gives the command's kind word, a reference word, and the reason, and the book does not change.  The reference word is the client tag for `limit` and `market`, the order id for `cancel` and `reduce`, and 0 otherwise.  For a record that is not seven words long, the kind word and the reference word are both 0.  The checks run in this order, and the first that fails gives the reason:

| Command | Checks, in order |
|---|---|
| Every command | Record of exactly seven words, then a known command kind |
| `limit` | Side, time in force, price from 1 to 1,023, quantity from 1 to 2^32 − 1, and, for post-only, an opposite side that it does not cross |
| `market` | Side, quantity from 1 to 2^32 − 1 |
| `cancel` | Resting order with the id, then the same account |
| `reduce` | Resting order with the id, then the same account, then a new quantity from 1 to 2^32 − 1, then a new quantity below the remaining quantity |

## Records

Commands and events are records of seven 64-bit words, and unused words of a command are ignored.  Unused words of an event are 0.  A stream of commands is a sequence of words that the book reads as consecutive seven-word records, and a shorter final record is rejected as malformed.  A stream whose length is a multiple of seven has no shorter record, and an empty stream has no records and no events.

| Command | Word 0 | Words 1 to 6 |
|---|---|---|
| `limit` | 1 | side, price, quantity, account, client tag, time in force |
| `market` | 2 | side, quantity, account, client tag |
| `cancel` | 3 | order id, account |
| `reduce` | 4 | order id, account, new quantity |

The side is 0 for buy and 1 for sell, and the time in force is 0 for GTC, 1 for IOC, and 2 for post-only.

| Event | Word 0 | Words 1 to 6 |
|---|---|---|
| `accepted` | 1 | order id, client tag |
| `rejected` | 2 | command kind word, reference word, reason |
| `trade` | 3 | maker id, taker id, price, quantity, maker account, maker remaining quantity |
| `cancelled` | 4 | order id, remaining quantity, reason |
| `reduced` | 5 | order id, new quantity |

| Rejection reason | Code |
|---|---|
| Record not seven words | 1 |
| Unknown command kind | 2 |
| Side other than 0 or 1 | 3 |
| Time in force other than 0, 1, or 2 | 4 |
| Price outside 1 to 1,023 | 5 |
| Quantity outside 1 to 2^32 − 1 | 6 |
| No resting order with the id | 7 |
| Order of another account | 8 |
| Post-only order that would cross | 9 |
| New quantity not below the remaining quantity | 10 |

| Cancellation reason | Code |
|---|---|
| Requested | 1 |
| IOC remainder | 2 |
| Self-trade prevention | 3 |
| Book full | 4 |

## Top of book

A query of the book, separate from the command stream, gives the best bid price and the total remaining quantity of the bids at that price, and the best ask price and the total remaining quantity of the asks at that price, with 0 for both values of an empty side.  A total is at most 4,096 × (2^32 − 1), which is below 2^44.
