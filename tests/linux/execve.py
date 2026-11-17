# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Runs a program with an argument vector and an environment given verbatim, through execve(2):
`execve.py PATH ARG... -- ENV...`.  The arguments between PATH and `--` form argv, which may be
empty, and the strings after `--` form envp, which may hold empty strings, strings without '=',
and repeated names, none of which env(1) or a shell can pass."""
import ctypes
import os
import sys

libc = ctypes.CDLL(None, use_errno=True)
sep = sys.argv.index("--")
path = os.fsencode(sys.argv[1])
argv = [os.fsencode(a) for a in sys.argv[2:sep]]
envp = [os.fsencode(e) for e in sys.argv[sep + 1 :]]
Argv = ctypes.c_char_p * (len(argv) + 1)
Envp = ctypes.c_char_p * (len(envp) + 1)
libc.execve(path, Argv(*argv, None), Envp(*envp, None))
err = ctypes.get_errno()
sys.exit(f"execve: {os.strerror(err)}")
