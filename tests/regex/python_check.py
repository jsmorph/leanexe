"""Checks the answers of Library.Regex.matchWith against Python's re.fullmatch.

Reads the lines that tests/TestSupport/Regex/PythonCases.lean writes: the postfix pattern words,
the input bytes in hexadecimal, and the matcher's answer, separated by '|'.  It decodes each
pattern as Library.Regex.Spec does, translates it to Python's syntax with a group around every
operand, and compares the answer with re.fullmatch on bytes.  It exits with status 1 at the
first difference and reports the number of cases otherwise.
"""

import re
import sys


def decode(words):
    """The Python pattern and the number of sets, or None when the words do not decode."""
    stack = []
    sets = 0
    i = 0
    while i < len(words):
        op = words[i]
        if op == 0:
            stack.append("(?!)")
        elif op == 1:
            stack.append("(?:)")
        elif op == 2:
            if i + 4 >= len(words):
                return None
            members = [b for b in range(256) if (words[i + 1 + b // 64] >> (b % 64)) & 1]
            i += 4
            sets += 1
            if members:
                stack.append("[" + "".join("\\x%02x" % b for b in members) + "]")
            else:
                stack.append("[^\\x00-\\xff]")
        elif op in (3, 4):
            if len(stack) < 2:
                return None
            b = stack.pop()
            a = stack.pop()
            stack.append("(?:%s)(?:%s)" % (a, b) if op == 3 else "(?:%s|%s)" % (a, b))
        elif op == 5:
            if not stack:
                return None
            stack.append("(?:%s)*" % stack.pop())
        else:
            return None
        i += 1
    if len(stack) != 1:
        return None
    return stack[0], sets


def answer(words, data):
    decoded = decode(words)
    if decoded is None:
        return 2
    pattern, sets = decoded
    if sets > 63:
        return 3
    return 1 if re.fullmatch(pattern.encode("ascii"), data, re.DOTALL) else 0


def main():
    count = 0
    for line in sys.stdin:
        line = line.strip()
        if not line:
            continue
        words_text, data_text, got_text = line.split("|")
        words = [int(w) for w in words_text.split(",")] if words_text else []
        want = answer(words, bytes.fromhex(data_text))
        if want != int(got_text):
            print("difference: %s: matcher %s, re.fullmatch %s" % (line, got_text, want))
            sys.exit(1)
        count += 1
    print("python: %d cases agree with re.fullmatch" % count)


main()
