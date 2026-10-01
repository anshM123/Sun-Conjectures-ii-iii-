# Two conjectures of Sun on OEIS A217703 are false

**Authors:** Ansh Mishra, Aryan Senthilkumar. **License:** MIT. **Paper:** [`paper/main.pdf`](paper/main.pdf)

[OEIS A217703](https://oeis.org/A217703) is defined by `a(0) = 1`, `a(1) = 0` and `a(n+1) = 2n(n+1) a(n) − n⁴ a(n−1)`.
Z.-W. Sun (2013) conjectured:
- (ii) `a(n) < 0` iff `1 < n < 58` or `n > 2177`;
- (iii) `|a(n)|^(1/n) = o(n²)`.

Google DeepMind's [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) states them as
`OeisA217703.conjecture2` and `conjecture3` (`research open`) in pull request
[#6426](https://github.com/google-deepmind/formal-conjectures/pull/6426).

**Both are false.**
- (ii): `a(81935) > 0`. This is exact: a 2,438,297-bit integer, computed in `scripts/exact_signs.py`. The signs change
  at `n = 2, 58, 2178, 81935`; the next change is near 3,082,582.
- (iii): `limsup |a(n)|^(1/n) / n² = e⁻²`, not 0.
  - Put `b = a/(n!)²` and let `v` be the second solution.
  - The Casoratian is `b(n)v(n−1) − b(n−1)v(n) = −1/n²`, and `|v(n)| ≤ n`.
  - Together these force `max(|b(n)|, |b(n−1)|) ≥ 1/(2n³)`.

## Lean 4 verification of (iii) (`lean/`)

- `Statement.lean`: the pull-request file, byte-identical (git blob `9beb5597`), compiled with the repository's
  `leanOptions`.
- `Core.lean` (Mathlib only): the copied `a`. It proves, in integers, the Casoratian identity
  `a(k+1)w(k) − a(k)w(k+1) = −(k!)⁴` and the bound `|a(n)|^(1/n)/n² ≥ 1/108` for infinitely many `n`.
- `Solution.lean`: `OeisA217703.conjecture3_false : ¬ <the repository statement>`.
- `CheckAnswer.lean`: `(¬ type_of% conjecture3) = type_of% conjecture3_false` by `rfl`; the definitions agree.
  Axioms: only `propext`, `Classical.choice` and `Quot.sound`.

To reproduce, you need:
- Lean v4.33.1;
- a formal-conjectures checkout, tested at `ab0addc45f699bdd0b7cc58efa5140a72f101a9e`;
- `lake exe cache get`, run in that checkout.

Then run:

```bash
bash lean/check.sh /path/to/formal-conjectures
```

Log: `logs/lean_check.log` (exit 0, 90 s).

Part (ii) is a computation with integers of millions of bits. We did not formalize it.

## Checks (`scripts/`, `logs/`)

- `exact_signs.py`: the exact signs of `a(n)` for `n ≤ 81940`. Runs in about 15 s.
- `casoratian_check.py`: the lemmas, with exact rationals, for `n < 3000`; and `|a(n)|^(1/n)/n²` approaching `e⁻²`.

## Prior work

The conjectures are in the OEIS entry (Sun, 2013), still listed as open. Search date 2026-10-01. We found no
counterexample or proof in:
- Formal Conjectures issues and pull requests;
- the OEIS Open benchmark (which covers only conjecture (i), irreducibility);
- GitHub;
- web search.
