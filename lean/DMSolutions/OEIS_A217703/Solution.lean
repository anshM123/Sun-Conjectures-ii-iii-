import DMSolutions.OEIS_A217703.Statement
import DMSolutions.OEIS_A217703.Core

/-!
# Disproof of `OeisA217703.conjecture3`

The statement is that of `FormalConjectures/OEIS/217703.lean` (formal-conjectures pull request
6426), included unmodified as `Statement.lean`. Its negation is stated here with the repository's
own definition `OeisA217703.a`, which agrees with the copy `A217703Core.a` by `rfl`.

`|a(n)|^(1/n) / n^2` does not tend to `0`: it is at least `1/108` for infinitely many `n`.
-/

namespace OeisA217703

theorem a_eq_core : a = A217703Core.a := by
  set_option smartUnfolding false in with_unfolding_all rfl

theorem conjecture3_false :
    ¬ Filter.Tendsto (fun n : ℕ => |(a n : ℝ)| ^ (1 / (n : ℝ)) / (n : ℝ) ^ 2)
      Filter.atTop (nhds 0) := by
  rw [a_eq_core]
  exact A217703Core.not_tendsto

end OeisA217703
