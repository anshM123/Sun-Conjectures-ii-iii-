"""Exact integer evaluation of A217703: a(0) = 1, a(1) = 0, a(n+1) = 2n(n+1) a(n) - n^4 a(n-1).

Reports the sign of a(n) around the predicted sign changes. Conjecture (ii) of Sun says
a(n) < 0 iff 1 < n < 58 or n > 2177; this computation shows a(81935) > 0.

Usage: python exact_signs.py          (pure Python integers, about 20 s)
"""
import time

N = 81940
WATCH = (2, 57, 58, 2177, 2178, 81933, 81934, 81935, 81936, 81937, 81938, 81939, 81940)
t0 = time.time()
a_prev, a = 1, 0                      # a(0), a(1)
sign = {0: 1, 1: 0}
changes = []
last = None
for n in range(1, N):
    a_prev, a = a, 2 * n * (n + 1) * a - n ** 4 * a_prev   # a is now a(n+1)
    m = n + 1
    s = (a > 0) - (a < 0)
    if m in WATCH:
        sign[m] = s
    if last is not None and s != last and s != 0:
        changes.append(m)
    if s != 0:
        last = s
    if m == 81935:
        print(f"a(81935) has {a.bit_length()} bits and sign {'+' if s > 0 else '-'}", flush=True)
print("signs:", {k: ('+' if v > 0 else '-' if v < 0 else '0') for k, v in sorted(sign.items())})
print("sign changes (first index of the new sign) up to", N, ":", changes)
print(f"time {time.time() - t0:.1f} s")
