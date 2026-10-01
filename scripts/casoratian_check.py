"""Exact checks for the disproof of conjecture (iii) of A217703 (|a(n)|^(1/n) = o(n^2)).

With b(n) = a(n)/(n!)^2 and the second solution v (v(0) = 0, v(1) = 1) of
(n+1)^2 b(n+1) = 2n(n+1) b(n) - n^2 b(n-1), the paper uses:
  (1) |v(n)| <= n for n >= 1,
  (2) the Casoratian b(n) v(n-1) - b(n-1) v(n) = -1/n^2,
  (3) max(|b(n)|, |b(n-1)|) >= 1/(2 n^3),
  (4) |b(n)| <= n.
All are checked here with exact rationals for n < 3000, and |a(n)|^(1/n)/n^2 is printed.

Usage: python casoratian_check.py [N]
"""
import math
import sys
from fractions import Fraction as Fr

N = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
b = [Fr(1), Fr(0)]
v = [Fr(0), Fr(1)]
for n in range(1, N):
    b.append((2 * n * (n + 1) * b[n] - n * n * b[n - 1]) / (n + 1) ** 2)
    v.append((2 * n * (n + 1) * v[n] - n * n * v[n - 1]) / (n + 1) ** 2)
ok = True
for n in range(1, N):
    ok &= abs(v[n]) <= n
    ok &= b[n] * v[n - 1] - b[n - 1] * v[n] == Fr(-1, n * n)
    ok &= abs(b[n]) <= n
    if n >= 2:
        ok &= max(abs(b[n]), abs(b[n - 1])) >= Fr(1, 2 * n ** 3)
print(f"checks (1)-(4) for 1 <= n < {N}:", "OK" if ok else "FAILED")
for n in (100, 500, 1000, 2000, N - 1):
    an = b[n] * math.factorial(n) ** 2
    if an != 0:
        lg = (math.log(abs(an.numerator)) - math.log(an.denominator)) / n - 2 * math.log(n)
        print(f"n = {n}: |a(n)|^(1/n)/n^2 = {math.exp(lg):.5f}   (e^-2 = {math.exp(-2):.5f})")
