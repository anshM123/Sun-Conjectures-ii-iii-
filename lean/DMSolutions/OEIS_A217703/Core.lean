import Mathlib

/-!
# OEIS A217703: `|a(n)|^(1/n) / n^2` does not tend to `0`

This file contains a verbatim copy of `OeisA217703.a` from `FormalConjectures/OEIS/217703.lean`
(formal-conjectures pull request 6426) and a proof that `|a(n)|^(1/n) / n^2` does not tend to `0`
(`not_tendsto`). In fact `|a(n)|^(1/n) / n^2 ≥ 1/108` for infinitely many `n`.

* `w` solves the recurrence of `a` with `w 0 = 0` and `w 1 = 1`.
* `casoratian`: `a (k + 1) * w k - a k * w (k + 1) = -(k!)^4`.
* `abs_w_le`: `|w n| ≤ 3^n (n!)^2`.
* `pow_le_three_pow_mul_factorial`: `n^n ≤ 3^n n!`, from `n^n / n! ≤ e^n`.
* `key`: for every `k` there is `n ≥ k` with `(n^n)^2 ≤ 6 (3^n)^3 (n + 1)^2 |a n|`. Indeed the
  first two items give `(k!)^4 ≤ |a (k + 1)| 3^k (k!)^2 + |a k| 3^(k+1) ((k + 1)!)^2`, so one of
  `|a k|`, `|a (k + 1)|` is large compared with `(k!)^2`; then use the third item.
* `not_tendsto`: if the quotient tended to `0`, then eventually `|a n| 108^n < (n^n)^2`, and `key`
  would give `4^n < 6 (n + 1)^2` for some `n ≥ 5`, which is false.
-/

namespace A217703Core

/-- `a n` is the sequence defined by $a(0)=1$, $a(1)=0$, and
$a(n+1) = 2n(n+1)a(n) - n^4 a(n-1)$ for $n > 0$. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 0
  | k + 2 =>
    let m : ℤ := k + 1
    (2 * m * (m + 1)) * a (k + 1) - (m ^ 4) * a k

/-- The solution of the recurrence of `a` with `w 0 = 0` and `w 1 = 1`. -/
def w : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | k + 2 => 2 * ((k : ℤ) + 1) * ((k : ℤ) + 1 + 1) * w (k + 1) - ((k : ℤ) + 1) ^ 4 * w k

theorem a_add_two (k : ℕ) :
    a (k + 2) = 2 * ((k : ℤ) + 1) * ((k : ℤ) + 1 + 1) * a (k + 1) - ((k : ℤ) + 1) ^ 4 * a k :=
  rfl

theorem w_add_two (k : ℕ) :
    w (k + 2) = 2 * ((k : ℤ) + 1) * ((k : ℤ) + 1 + 1) * w (k + 1) - ((k : ℤ) + 1) ^ 4 * w k :=
  rfl

theorem factorial_succ_cast (n : ℕ) :
    (((n + 1).factorial : ℕ) : ℤ) = ((n : ℤ) + 1) * (n.factorial : ℤ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one]

theorem abs_mul_sub_mul_le (x y u v : ℤ) : |x * u - y * v| ≤ |x| * |u| + |y| * |v| := by
  calc |x * u - y * v| ≤ |x * u| + |y * v| := abs_sub _ _
    _ = |x| * |u| + |y| * |v| := by rw [abs_mul, abs_mul]

theorem abs_mul_sub_mul_le_of_nonneg {x y : ℤ} (u v : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |x * u - y * v| ≤ x * |u| + y * |v| := by
  calc |x * u - y * v| ≤ |x| * |u| + |y| * |v| := abs_mul_sub_mul_le x y u v
    _ = x * |u| + y * |v| := by rw [abs_of_nonneg hx, abs_of_nonneg hy]

/-- The Casoratian of `a` and `w`. -/
theorem casoratian (k : ℕ) :
    a (k + 1) * w k - a k * w (k + 1) = -((k.factorial : ℤ) ^ 4) := by
  induction k with
  | zero => norm_num [a, w]
  | succ k ih =>
    rw [show k + 1 + 1 = k + 2 from rfl, a_add_two, w_add_two, factorial_succ_cast]
    linear_combination ((k : ℤ) + 1) ^ 4 * ih

/-- `|w n| ≤ 3^n (n!)^2`. -/
theorem abs_w_le : ∀ n : ℕ, |w n| ≤ 3 ^ n * ((n.factorial : ℕ) : ℤ) ^ 2
  | 0 => by norm_num [w]
  | 1 => by norm_num [w]
  | k + 2 => by
    have h1 := abs_w_le (k + 1)
    have h0 := abs_w_le k
    rw [factorial_succ_cast] at h1
    show |w (k + 2)| ≤ 3 ^ (k + 2) * (((k + 1 + 1).factorial : ℕ) : ℤ) ^ 2
    rw [w_add_two, factorial_succ_cast (k + 1), factorial_succ_cast k, Nat.cast_add_one]
    have hX : (0 : ℤ) ≤ 3 ^ k * (k.factorial : ℤ) ^ 2 * ((k : ℤ) + 1) ^ 2 *
        (2 * ((k : ℤ) + 1) ^ 2 + 12 * ((k : ℤ) + 1) + 9) := by positivity
    have e : 3 ^ (k + 2) * (((k : ℤ) + 1 + 1) * (((k : ℤ) + 1) * (k.factorial : ℤ))) ^ 2 -
        (2 * ((k : ℤ) + 1) * ((k : ℤ) + 1 + 1) *
          (3 ^ (k + 1) * (((k : ℤ) + 1) * (k.factorial : ℤ)) ^ 2) +
          ((k : ℤ) + 1) ^ 4 * (3 ^ k * (k.factorial : ℤ) ^ 2)) =
        3 ^ k * (k.factorial : ℤ) ^ 2 * ((k : ℤ) + 1) ^ 2 *
          (2 * ((k : ℤ) + 1) ^ 2 + 12 * ((k : ℤ) + 1) + 9) := by ring
    calc |2 * ((k : ℤ) + 1) * ((k : ℤ) + 1 + 1) * w (k + 1) - ((k : ℤ) + 1) ^ 4 * w k|
        ≤ 2 * ((k : ℤ) + 1) * ((k : ℤ) + 1 + 1) * |w (k + 1)| + ((k : ℤ) + 1) ^ 4 * |w k| :=
          abs_mul_sub_mul_le_of_nonneg _ _ (by positivity) (by positivity)
      _ ≤ 2 * ((k : ℤ) + 1) * ((k : ℤ) + 1 + 1) *
            (3 ^ (k + 1) * (((k : ℤ) + 1) * (k.factorial : ℤ)) ^ 2) +
            ((k : ℤ) + 1) ^ 4 * (3 ^ k * (k.factorial : ℤ) ^ 2) := by
          gcongr
      _ ≤ 3 ^ (k + 2) * (((k : ℤ) + 1 + 1) * (((k : ℤ) + 1) * (k.factorial : ℤ))) ^ 2 := by
          linarith

/-- `n^n ≤ 3^n n!`. -/
theorem pow_le_three_pow_mul_factorial (n : ℕ) : n ^ n ≤ 3 ^ n * n.factorial := by
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h1 : (n : ℝ) ^ n / n.factorial ≤ Real.exp n :=
    Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
  have h2 : Real.exp n ≤ 3 ^ n := by
    rw [← mul_one (n : ℝ), Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le n
  rw [div_le_iff₀ hf] at h1
  have h3 : (n : ℝ) ^ n ≤ 3 ^ n * n.factorial :=
    h1.trans (mul_le_mul_of_nonneg_right h2 hf.le)
  exact_mod_cast h3

/-- For every `k` there is `n ≥ k` with `(n^n)^2 ≤ 6 (3^n)^3 (n + 1)^2 |a n|`. -/
theorem key (k : ℕ) :
    ∃ n, k ≤ n ∧ ((n : ℤ) ^ n) ^ 2 ≤ 6 * (3 ^ n) ^ 3 * ((n : ℤ) + 1) ^ 2 * |a n| := by
  have hFpos : (0 : ℤ) < (k.factorial : ℤ) := by exact_mod_cast Nat.factorial_pos k
  have hF2 : (0 : ℤ) < (k.factorial : ℤ) ^ 2 := by positivity
  have hw0 := abs_w_le k
  have hw1 := abs_w_le (k + 1)
  rw [factorial_succ_cast] at hw1
  have hF4 : (k.factorial : ℤ) ^ 4 ≤ |a (k + 1)| * (3 ^ k * (k.factorial : ℤ) ^ 2) +
      |a k| * (3 ^ (k + 1) * (((k : ℤ) + 1) * (k.factorial : ℤ)) ^ 2) := by
    have e : (k.factorial : ℤ) ^ 4 = |a (k + 1) * w k - a k * w (k + 1)| := by
      rw [casoratian, abs_neg, abs_of_nonneg (by positivity)]
    rw [e]
    calc |a (k + 1) * w k - a k * w (k + 1)| ≤ |a (k + 1)| * |w k| + |a k| * |w (k + 1)| :=
          abs_mul_sub_mul_le _ _ _ _
      _ ≤ |a (k + 1)| * (3 ^ k * (k.factorial : ℤ) ^ 2) +
          |a k| * (3 ^ (k + 1) * (((k : ℤ) + 1) * (k.factorial : ℤ)) ^ 2) := by gcongr
  by_cases hcase : (k.factorial : ℤ) ^ 4 ≤
      2 * (|a k| * (3 ^ (k + 1) * (((k : ℤ) + 1) * (k.factorial : ℤ)) ^ 2))
  · -- `n = k`
    refine ⟨k, le_rfl, ?_⟩
    have h1 : (k.factorial : ℤ) ^ 2 ≤ 2 * 3 ^ (k + 1) * ((k : ℤ) + 1) ^ 2 * |a k| := by
      refine le_of_mul_le_mul_left ?_ hF2
      calc (k.factorial : ℤ) ^ 2 * (k.factorial : ℤ) ^ 2 = (k.factorial : ℤ) ^ 4 := by ring
        _ ≤ 2 * (|a k| * (3 ^ (k + 1) * (((k : ℤ) + 1) * (k.factorial : ℤ)) ^ 2)) := hcase
        _ = (k.factorial : ℤ) ^ 2 * (2 * 3 ^ (k + 1) * ((k : ℤ) + 1) ^ 2 * |a k|) := by ring
    have h2 : (k : ℤ) ^ k ≤ 3 ^ k * (k.factorial : ℤ) := by
      exact_mod_cast pow_le_three_pow_mul_factorial k
    have h3 : ((k : ℤ) ^ k) ^ 2 ≤ (3 ^ k * (k.factorial : ℤ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    calc ((k : ℤ) ^ k) ^ 2 ≤ (3 ^ k * (k.factorial : ℤ)) ^ 2 := h3
      _ = (3 ^ k) ^ 2 * (k.factorial : ℤ) ^ 2 := by ring
      _ ≤ (3 ^ k) ^ 2 * (2 * 3 ^ (k + 1) * ((k : ℤ) + 1) ^ 2 * |a k|) := by gcongr
      _ = 6 * (3 ^ k) ^ 3 * ((k : ℤ) + 1) ^ 2 * |a k| := by ring
  · -- `n = k + 1`
    have hcase2 : (k.factorial : ℤ) ^ 4 ≤ 2 * (|a (k + 1)| * (3 ^ k * (k.factorial : ℤ) ^ 2)) := by
      have := not_le.mp hcase
      linarith
    refine ⟨k + 1, Nat.le_succ k, ?_⟩
    have h1 : (k.factorial : ℤ) ^ 2 ≤ 2 * 3 ^ k * |a (k + 1)| := by
      refine le_of_mul_le_mul_left ?_ hF2
      calc (k.factorial : ℤ) ^ 2 * (k.factorial : ℤ) ^ 2 = (k.factorial : ℤ) ^ 4 := by ring
        _ ≤ 2 * (|a (k + 1)| * (3 ^ k * (k.factorial : ℤ) ^ 2)) := hcase2
        _ = (k.factorial : ℤ) ^ 2 * (2 * 3 ^ k * |a (k + 1)|) := by ring
    have h2 : ((k + 1 : ℕ) : ℤ) ^ (k + 1) ≤ 3 ^ (k + 1) * (((k : ℤ) + 1) * (k.factorial : ℤ)) := by
      rw [← factorial_succ_cast]
      exact_mod_cast pow_le_three_pow_mul_factorial (k + 1)
    have h3 : (((k + 1 : ℕ) : ℤ) ^ (k + 1)) ^ 2 ≤
        (3 ^ (k + 1) * (((k : ℤ) + 1) * (k.factorial : ℤ))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h2 2
    have hX : (0 : ℤ) ≤ (3 ^ k) ^ 3 * |a (k + 1)| * (144 * (k : ℤ) ^ 2 + 612 * (k : ℤ) + 630) := by
      positivity
    have e : 6 * (3 ^ (k + 1)) ^ 3 * ((k : ℤ) + 1 + 1) ^ 2 * |a (k + 1)| -
        9 * (3 ^ k) ^ 2 * ((k : ℤ) + 1) ^ 2 * (2 * 3 ^ k * |a (k + 1)|) =
        (3 ^ k) ^ 3 * |a (k + 1)| * (144 * (k : ℤ) ^ 2 + 612 * (k : ℤ) + 630) := by ring
    calc (((k + 1 : ℕ) : ℤ) ^ (k + 1)) ^ 2
        ≤ (3 ^ (k + 1) * (((k : ℤ) + 1) * (k.factorial : ℤ))) ^ 2 := h3
      _ = 9 * (3 ^ k) ^ 2 * ((k : ℤ) + 1) ^ 2 * (k.factorial : ℤ) ^ 2 := by ring
      _ ≤ 9 * (3 ^ k) ^ 2 * ((k : ℤ) + 1) ^ 2 * (2 * 3 ^ k * |a (k + 1)|) := by gcongr
      _ ≤ 6 * (3 ^ (k + 1)) ^ 3 * (((k + 1 : ℕ) : ℤ) + 1) ^ 2 * |a (k + 1)| := by
          rw [Nat.cast_add_one]
          linarith

/-- `6 (n + 1)^2 ≤ 4^n` for `n ≥ 5`. -/
theorem six_mul_sq_le_four_pow (n : ℕ) (hn : 5 ≤ n) : 6 * (n + 1) ^ 2 ≤ 4 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ (4 : ℕ) n]
    nlinarith [ih]

/-- `|a(n)|^(1/n) / n^2` does not tend to `0`. -/
theorem not_tendsto :
    ¬ Filter.Tendsto (fun n : ℕ => |(a n : ℝ)| ^ (1 / (n : ℝ)) / (n : ℝ) ^ 2)
      Filter.atTop (nhds 0) := by
  intro h
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 ((tendsto_order.1 h).2 (1 / 108) (by norm_num))
  obtain ⟨n, hn, hkey⟩ := key (N + 5)
  have hfn : |(a n : ℝ)| ^ (1 / (n : ℝ)) / (n : ℝ) ^ 2 < 1 / 108 := hN n (by omega)
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  rw [div_lt_iff₀ (pow_pos hnpos 2)] at hfn
  -- `|a n| < (n^2 / 108)^n`, i.e. `|a n| 108^n < (n^n)^2`
  have hlt : |(a n : ℝ)| * 108 ^ n < ((n : ℝ) ^ n) ^ 2 := by
    have h0 : 0 ≤ |(a n : ℝ)| ^ (1 / (n : ℝ)) := by positivity
    have h1 := pow_lt_pow_left₀ hfn h0 hn0
    rw [one_div (n : ℝ), Real.rpow_inv_natCast_pow (abs_nonneg _) hn0] at h1
    calc |(a n : ℝ)| * 108 ^ n < (1 / 108 * (n : ℝ) ^ 2) ^ n * 108 ^ n :=
          mul_lt_mul_of_pos_right h1 (by positivity)
      _ = ((n : ℝ) ^ n) ^ 2 := by
          rw [← mul_pow, show 1 / 108 * (n : ℝ) ^ 2 * 108 = (n : ℝ) ^ 2 by ring, ← pow_mul,
            ← pow_mul, mul_comm]
  have hkeyR : ((n : ℝ) ^ n) ^ 2 ≤ 6 * (3 ^ n) ^ 3 * ((n : ℝ) + 1) ^ 2 * |(a n : ℝ)| := by
    exact_mod_cast hkey
  have h108 : (108 : ℝ) ^ n = 4 ^ n * (3 ^ n) ^ 3 := by
    rw [← pow_mul, mul_comm n 3, pow_mul, ← mul_pow]
    norm_num
  have hP : (0 : ℝ) < ((n : ℝ) ^ n) ^ 2 * (3 ^ n) ^ 3 := by positivity
  have h1 : ((n : ℝ) ^ n) ^ 2 * (3 ^ n) ^ 3 * 4 ^ n <
      ((n : ℝ) ^ n) ^ 2 * (3 ^ n) ^ 3 * (6 * ((n : ℝ) + 1) ^ 2) := by
    calc ((n : ℝ) ^ n) ^ 2 * (3 ^ n) ^ 3 * 4 ^ n = ((n : ℝ) ^ n) ^ 2 * 108 ^ n := by
          rw [h108]; ring
      _ ≤ 6 * (3 ^ n) ^ 3 * ((n : ℝ) + 1) ^ 2 * |(a n : ℝ)| * 108 ^ n :=
          mul_le_mul_of_nonneg_right hkeyR (by positivity)
      _ = 6 * (3 ^ n) ^ 3 * ((n : ℝ) + 1) ^ 2 * (|(a n : ℝ)| * 108 ^ n) := by ring
      _ < 6 * (3 ^ n) ^ 3 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) ^ n) ^ 2 :=
          mul_lt_mul_of_pos_left hlt (by positivity)
      _ = ((n : ℝ) ^ n) ^ 2 * (3 ^ n) ^ 3 * (6 * ((n : ℝ) + 1) ^ 2) := by ring
  have h2 := lt_of_mul_lt_mul_left h1 hP.le
  have h3 : 6 * ((n : ℝ) + 1) ^ 2 ≤ 4 ^ n := by
    exact_mod_cast six_mul_sq_le_four_pow n (by omega)
  linarith

end A217703Core
