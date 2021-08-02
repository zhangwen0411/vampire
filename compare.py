#!/usr/bin/env python3

from subprocess import run, DEVNULL
from time import monotonic


def vampire(vampire, problem):
    start = monotonic()
    status = run([
        vampire,
	'--input_syntax', 'tptp',
	'-sa', 'discount',
        '-t', '10',
        f"Problems/{problem[:3]}/{problem}.p",
    ], stdout=DEVNULL, stderr=DEVNULL)
    if status.returncode == 0:
        end = monotonic()
        elapsed = end - start
        return elapsed
    else:
        return float('inf')


if __name__ == '__main__':
    from sys import argv
    problem = argv[1]
    regular = vampire('./vampire', problem)
    shared = vampire('./vampire-shared', problem)
    print(f"{problem},{regular},{shared}")
