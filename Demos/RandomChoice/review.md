# Reviews of the specification

Two fresh agents reviewed [the specification](Spec.lean) and [the samples](Samples.lean) against
[the request](request.txt), as step 5 of [the verified-request
skill](../../.claude/skills/verified-request/SKILL.md) describes.  Each received only the paths of
the request, the specification, the samples, and the samples' outputs, wrote its own model of the
request in Python, compared it with every output, and ran no Lean code of the repository.

## First review

The first review found no disagreement.  Its model agreed with the 119 outputs of the first sample
set and with a transcription of the specification on 200,000 random inputs for each function,
weighted toward zero bytes, the bytes beside the digits, numerals near `2^64`, and words near
`2^64 mod N`.  It confirmed by arithmetic for 20,011 values of N, and by an exhaustive count with
10-bit words, that every value in [1, N] has `⌊2^64 / N⌋` accepted words.  It found three comments
imprecise: the comment of `argument` did not say that zero bytes are counted from 1, the module
comment did not say that a missing argument is refused, and it stated the command's reading of N
and K without saying that the command's specification carries that choice.  The specification's
comments now state all three.

The review named input classes that no sample covered, and the samples now cover each: argument 0
with an empty program name and of the empty buffer, an overflowing numeral followed by a letter,
`N = 2^63 - 1` and `N = 3 · 2^62`, whose remainders 2 and `2^62` no other sample has, and the
powers of two 4 and `2^32`.

## Second review

The second review, of the revised specification and its 132 samples, found no disagreement.  Its
model, built from the request alone, and a transcription of the specification agreed with every
output and with each other on 200,000 random inputs weighted toward zero bytes, values near
`2^64`, powers of two, and words at `2^64 mod N`.  A check over 1,008 values of N confirmed that
each value in [1, N] has `⌊2^64 / N⌋` accepted words.  It found every open case recorded and
named three notes on the comments, which this review records without changing the frozen files.

| Note | Response |
|---|---|
| The comment names the command's specification as the place where N is argument 1, K argument 2, and the later arguments are ignored, which no file of the specification defines | [The command's specification](CommandSpec.lean) reads N and K as arguments 1 and 2 with `parseSpec`, and no event of a run depends on the other arguments |
| WASI's documentation of `args_get` does not state the layout of the buffer | `LeanExe.Wasi.args` passes the bytes of `args_get` to the program, and Wasmtime writes each argument followed by a zero byte, as the histogram's runs and the command's runs show |
| The request's formula `(0 - N) % N` accepts every word for N = 0, while `pickSpec` accepts none | `pick` tests `n != 0`, and `pick_eq` proves it equal to `pickSpec` for every N, 0 included |

It named these classes that no sample covers, which step 7 of the skill records without new
samples:

| Function | Class |
|---|---|
| `parseArg` | Numerals of more than 21 significant digits, which an accumulator wider than 64 bits would read differently |
| `pick` | An N with `2^64 mod N = N - 1`, the largest threshold, such as 274,177, a divisor of `2^64 + 1` |
| `render` | The boundaries 9,999 and 10,000, 999,999 and 1,000,000, and `10^k - 1` and `10^k` for k from 7 to 18 |

`parseArg_eq` and `pick_eq` prove the programs equal to the specifications on every input, and
`render_eq` on every array of fewer than `2^59` values, so an error of a program in these classes
would contradict those theorems.

# Reviews of the specification of `putPicks`

Two fresh agents reviewed [the specification of `putPicks`](PicksSpec.lean) and [its
samples](PicksSamples.lean) against [the request](request.txt) and [the request that `putPicks`
serves](picks-request.txt), with the specifications of [the pure core](Spec.lean) that it uses.  Each
received only the paths of those files and of the samples' outputs, wrote its own model in Python,
compared it with every output, and ran no Lean code of the repository.

## First review

The first review found no input on which the specification contradicts the requests.  Its model,
built from the requests, and a transcription of the specification agreed with the 19 outputs of
the first sample set and with each other on 20,000 random inputs, among them 6,708 whose lines are
longer than the output buffer, 6,724 whose limit cuts the values, 593 with N = 0, 9,984 with bytes
after the last whole word, and 1,942 with more than 512 words.  It named notes on the comment and
input classes that no sample covered, with these responses.

| Note | Response |
|---|---|
| The comment does not record N = 0, which accepts no word | The comment states it and names `accepts` |
| The specification reads every whole word of the draw, which is right only when the command fills the whole draw buffer at each call | The comment states that the command fills the whole buffer of 4,096 bytes at each call of `random_get` |
| When the lines are longer than the buffer, the length and the count include lines that were dropped, which a caller that writes the length would get wrong | The comment states it, and that the command's buffer of 10,752 bytes holds the lines of 512 values of at most 20 digits, so the lines of a draw always fit |
| The heading of the decisions lists points that the request fixes | The comment separates what the request fixes from the choices that it leaves open |

The samples now cover each class that the review named: a buffer of varied bytes, lines longer
than a buffer that ends after a newline, lines that the limit cuts and that are longer than the
buffer, N of 2, `2^32`, and `2^63`, whose threshold is 0, 512 values of 20 digits, whose lines fill
10,752 bytes, and a draw of 600 words.

## Second review

The second review, of the revised specification and its 27 samples, found no disagreement.  Its
model, built from the requests and the comment's prose, rebuilt the 27 inputs from the samples'
file, agreed with every output, and agreed with a transcription of the specification on 200,000
random inputs weighted toward N at powers of two and their neighbors, words at the threshold and at
multiples of N, draws with trailing bytes, limits at the count of accepted words, and buffers at
the length of the lines.  It found every open case recorded and named two notes on the comment and
a remark on the design, which this review records without changing the frozen files.

| Note | Response |
|---|---|
| "every word of `draw` comes from the draw" means that no word of an earlier call is read again | The command fills the whole draw buffer at each call, which `Rounds` states of every pass with the event `random_get` of 4,096 bytes and its reply |
| The first decision lists the little-endian reading, which the request fixes; the open parts are the positions of the words and the bytes after the last whole word | The decision records both parts, and the request's reading agrees with it |
| When the lines are longer than `out`, the second component exceeds the filled window, which the command could not write | The command's buffer of 10,752 bytes holds the lines of every draw, and `pass_put` proves that the lines fit, so the command writes exactly the lines |

It named these classes that no sample covers, which step 7 of the skill records without new
samples: N ≥ 1 with a draw whose words are all rejected, a buffer that ends inside a line of two or
more digits, and counts of `2^64` or more, which need a draw of more than `2^67` bytes.
`putPicks_eq` proves the program equal to the specification on every draw of fewer than `2^32`
bytes, so an error of the program in the first two classes would contradict it.
