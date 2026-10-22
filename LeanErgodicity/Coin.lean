import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The 1.5 / 0.6 coin

Heads multiplies wealth by `3/2`, tails by `3/5`, each with probability `1/2`. This is the example
in *Ergodicity, Explained*.

* The expected factor of one toss is `21/20`, a 5% gain (`coin_ensemble_factor`).
* Expected wealth after `n` tosses is `(21/20)^n`, which grows without bound
  (`coin_expected_wealth`, `coin_expected_wealth_tendsto`).
* The time-average growth rate `½ log (3/2) + ½ log (3/5)` is negative (`coin_time_average_neg`).
* A path with as many heads as tails multiplies wealth by `(9/10)^n` every `2n` tosses, which goes
  to zero (`coin_balanced_path`, `coin_balanced_path_tendsto_zero`).
* The additive version of the bet (win 50, lose 40) has the same average over time and across
  players (`additive_time_average_eq_ensemble`).
-/

open Real Finset Filter Topology

namespace LeanErgodicity

/-- The expected growth factor of one toss is `21/20`. -/
theorem coin_ensemble_factor : (1 / 2 : ℝ) * (3 / 2) + 1 / 2 * (3 / 5) = 21 / 20 := by norm_num

/-- The growth rate of the average across players is positive. -/
theorem coin_ensemble_growth_pos : 0 < log (21 / 20 : ℝ) := log_pos (by norm_num)

/-- The time-average growth rate equals `½ log (9/10)`. -/
theorem coin_time_average_eq :
    (1 / 2 : ℝ) * log (3 / 2) + 1 / 2 * log (3 / 5) = 1 / 2 * log (9 / 10) := by
  rw [← mul_add, ← log_mul (by norm_num) (by norm_num)]
  norm_num

/-- The time-average growth rate of the coin is negative: one player repeating the bet loses. -/
theorem coin_time_average_neg : (1 / 2 : ℝ) * log (3 / 2) + 1 / 2 * log (3 / 5) < 0 := by
  rw [coin_time_average_eq]
  have := log_neg (by norm_num : (0 : ℝ) < 9 / 10) (by norm_num)
  linarith

/-- Expected wealth after `n` tosses, summing over the number of heads `k`, is `(21/20)^n`. -/
theorem coin_expected_wealth (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℝ) * (1 / 2) ^ n * ((3 / 2) ^ k * (3 / 5) ^ (n - k)) =
      (21 / 20) ^ n := by
  have h : (21 / 20 : ℝ) = 3 / 4 + 3 / 10 := by norm_num
  rw [h, add_pow]
  refine sum_congr rfl (fun k hk => ?_)
  have hk : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hsplit : (1 / 2 : ℝ) ^ n = (1 / 2) ^ k * (1 / 2) ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hk]
  rw [hsplit]
  have h34 : (3 / 4 : ℝ) ^ k = (1 / 2) ^ k * (3 / 2) ^ k := by rw [← mul_pow]; norm_num
  have h310 : (3 / 10 : ℝ) ^ (n - k) = (1 / 2) ^ (n - k) * (3 / 5) ^ (n - k) := by
    rw [← mul_pow]; norm_num
  rw [h34, h310]
  ring

/-- Expected wealth grows without bound. -/
theorem coin_expected_wealth_tendsto : Tendsto (fun n : ℕ => (21 / 20 : ℝ) ^ n) atTop atTop :=
  tendsto_pow_atTop_atTop_of_one_lt (by norm_num)

/-- `n` heads and `n` tails multiply wealth by `(9/10)^n`, whatever their order. -/
theorem coin_balanced_path (n : ℕ) : (3 / 2 : ℝ) ^ n * (3 / 5) ^ n = (9 / 10) ^ n := by
  rw [← mul_pow]
  norm_num

/-- On a path with as many heads as tails, wealth goes to zero. -/
theorem coin_balanced_path_tendsto_zero :
    Tendsto (fun n : ℕ => (3 / 2 : ℝ) ^ n * (3 / 5) ^ n) atTop (𝓝 0) := by
  simp_rw [coin_balanced_path]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- After 100 tosses with 50 heads, \$100 becomes less than \$1. -/
theorem coin_hundred_tosses : (100 : ℝ) * (3 / 2) ^ 50 * (3 / 5) ^ 50 < 1 := by norm_num

/-- **Additive bets are ergodic.** If a bet adds `a` or `b` to wealth with equal probability, a path
with `n` of each has the same average gain per round as the average across players. -/
theorem additive_time_average_eq_ensemble (a b : ℝ) {n : ℕ} (hn : 0 < n) :
    ((n : ℝ) * a + n * b) / (2 * n) = 1 / 2 * a + 1 / 2 * b := by
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

end LeanErgodicity
