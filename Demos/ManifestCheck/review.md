# Reviews of the specification

Two fresh agents reviewed [the specification](Spec.lean) and [the samples](Samples.lean) against
[the request](request.txt), as step 5 of [the verified-request
skill](../../.claude/skills/verified-request/SKILL.md) describes.  Each received only the paths of
the request, the specification, the samples, and the samples' outputs, wrote its own model of the
three functions in Python, compared it with every output, and ran no Lean code of the repository.

## First review

The first review found no disagreement.  Its model reproduced the 83 lines of output of the first
sample set and agreed with a second, separately written model on 200,000 random manifests and hex
windows.  It compared the choices of the comment with GNU `sha256sum` 9.7, which skips a line that
is not in the format with a warning and status 0, refuses a manifest with no line with status 1,
removes a trailing carriage return, accepts a single space or a tab before the name, accepts
leading blanks and the tagged form, skips comments, cuts a name at a zero byte, and escapes names
that hold a backslash, a carriage return, or a newline.  The specification differs from it in
each of these, and the comment records each choice.

The review asked for three changes of the comment, which the specification now makes.  The comment
stated the refusal of a single space or a tab only through the definition of the format, and it
now states it.  It stated only through "the name keeps every byte" that absolute names and names
with `..` components are in the format, and it now states that the format admits them and that the
host's resolution confines each open to the preopened directory.  It named the names for which
`sha256sum` writes the escaped form, and the review found a third, so the comment now says "some
names".  The review noted that the status of a refused manifest, and the wording of the verdict for
a manifest with no line, belong to the command's specification.

The review named input classes that no sample covered, and the samples now cover each: the bytes
`/`, `:`, `@`, `` ` ``, and `G` in the digits of a line and of a hex window, a backslash inside a
name, binary mode with a name that starts with `*` or a space, a malformed line between two lines
in the format, empty lines after the last line, a leading tab, a digest that differs only in its
second or third word or in a high half after byte 0, and a name with a backslash in an output line.

## Second review

The second review, of the revised specification and its 99 samples, found no disagreement and
found every open case recorded.  Its model agreed with all 99 outputs and with a transcription of
the specification on 200,000 random inputs, 13,786 of them accepted manifests and 38,415 matching
digests.  It compared the choices with GNU's `split_3`, `digest_check`, and `problematic_chars` in
coreutils `src/cksum.c`.  The specification departs from `sha256sum -c` in the trailing carriage
return, leading blanks, `#` lines, a tab or a single space before the name, escaped and tagged
lines, the refusal of a whole manifest for one line that is not in the format, and the escaping of
output names.  Each choice agrees with the request's literal `HEX  NAME` and `NAME: OK`.  The
review noted that whether "like `sha256sum -c`" asks for any of GNU's behaviors is the user's
decision.

It named these classes that no sample covers, which step 7 of the skill records without new
samples:

| Function | Class |
|---|---|
| `parseSpec`, `hexMatchesSpec` | A zero byte or a byte of 128 or more among the 64 digits |
| `parseSpec` | A carriage return inside a line, as in a manifest whose lines end in carriage returns alone |
| `parseSpec` | A name of one byte that is a space or `*` |
| `parseSpec` | A last line without a newline that is not in the format, after lines in the format |
| `hexMatchesSpec` | Text in upper or mixed case that does not match |

`parse_eq` and `hexMatches_eq` prove the program equal to the specification on every manifest of
the sizes that a store holds, so an error of the program in these classes would contradict those
theorems.  `tools/verified-request-check --freeze` supports only `Examples/<Name>/`, so
`spec.sha256` holds the output of `sha256sum` on `Spec.lean` and `Samples.lean`, and the demo's
driver checks it with `sha256sum -c`.
