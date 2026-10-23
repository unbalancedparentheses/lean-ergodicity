import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The St Petersburg paradox

A fair coin is tossed until it lands heads. If that takes `n + 1` tosses, which happens with
probability `(1/2)^(n+1)`, the game pays `2^n`. This is Peters and Gell-Mann's version
("Evaluating gambles using dynamics", 2016, §III).

* `stPetersburg_expected_payout_not_summable`: every outcome contributes `1/2` to the expected
  payout, so the expected payout is infinite and expected value says any fee is worth paying.
* `stPetersburg_growth_summable`: for a player with wealth `W` paying a fee `F < W`, the expected
  change in log wealth, `∑ (1/2)^(n+1) log ((W - F + 2^n) / W)`, is a convergent series. The
  time-average criterion gives every player a finite price for the game.
-/

open Real Finset

namespace LeanErgodicity

/-- Each outcome contributes exactly one half to the expected payout. -/
theorem stPetersburg_term (n : ℕ) : (1 / 2 : ℝ) ^ (n + 1) * 2 ^ n = 1 / 2 := by
  rw [pow_succ, mul_comm ((1 / 2 : ℝ) ^ n), mul_assoc, ← mul_pow]
  norm_num

/-- **The expected payout is infinite.** -/
theorem stPetersburg_expected_payout_not_summable :
    ¬ Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) * 2 ^ n) := by
  simp_rw [stPetersburg_term]
  intro h
  have := h.tendsto_atTop_zero
  have h' : (1 / 2 : ℝ) = 0 := tendsto_nhds_unique tendsto_const_nhds this
  norm_num at h'

/-- `log (a + 2^n)` grows at most linearly in `n`. -/
theorem abs_log_add_two_pow_le {a : ℝ} (ha : 0 < a) (n : ℕ) :
    |log (a + 2 ^ n)| ≤ |log a| + log (1 + 1 / a) + n * log 2 := by
  have h2n : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have hpos : 0 < a + 2 ^ n := by positivity
  have hsplit : log (a + 2 ^ n) = log a + log (1 + 2 ^ n / a) := by
    rw [← log_mul ha.ne' (by positivity)]
    congr 1
    field_simp
  have hq : 0 ≤ 2 ^ n / a := by positivity
  have hlow : 0 ≤ log (1 + 2 ^ n / a) := log_nonneg (by linarith)
  have hup : log (1 + 2 ^ n / a) ≤ log (1 + 1 / a) + n * log 2 := by
    rw [← log_pow, ← log_mul (by positivity) (by positivity)]
    apply log_le_log (by positivity)
    have : 2 ^ n / a ≤ (1 / a) * 2 ^ n := by rw [div_eq_mul_inv, one_div, mul_comm]
    nlinarith [show 0 ≤ 1 / a by positivity]
  rw [hsplit]
  calc |log a + log (1 + 2 ^ n / a)| ≤ |log a| + |log (1 + 2 ^ n / a)| := abs_add_le _ _
    _ = |log a| + log (1 + 2 ^ n / a) := by rw [abs_of_nonneg hlow]
    _ ≤ |log a| + log (1 + 1 / a) + n * log 2 := by linarith

/-- **The time-average value of the game is finite.** For wealth `W > 0` and a fee `F < W`, the
expected change in log wealth from playing once is a convergent series. -/
theorem stPetersburg_growth_summable {W F : ℝ} (hW : 0 < W) (hF : F < W) :
    Summable (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) * log ((W - F + 2 ^ n) / W)) := by
  have ha : 0 < W - F := by linarith
  set A := |log (W - F)| + log (1 + 1 / (W - F)) + |log W|
  have hgeo : Summable (fun n : ℕ => ((1 : ℝ) / 2) ^ n) := summable_geometric_two
  have hngeo : Summable (fun n : ℕ => (n : ℝ) ^ 1 * ((1 : ℝ) / 2) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
  refine Summable.of_norm_bounded
    ((hgeo.mul_left (A / 2)).add (hngeo.mul_left (log 2 / 2))) (fun n => ?_)
  have hpos : 0 < W - F + 2 ^ n := by positivity
  rw [log_div hpos.ne' hW.ne', Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  have hb := abs_log_add_two_pow_le ha n
  have hsub : |log (W - F + 2 ^ n) - log W| ≤ |log (W - F + 2 ^ n)| + |log W| := abs_sub _ _
  have hp : (1 / 2 : ℝ) ^ (n + 1) = 1 / 2 * (1 / 2) ^ n := by rw [pow_succ]; ring
  rw [hp, pow_one]
  have hn : (0 : ℝ) ≤ (1 / 2) ^ n := by positivity
  calc 1 / 2 * (1 / 2) ^ n * |log (W - F + 2 ^ n) - log W|
      ≤ 1 / 2 * (1 / 2) ^ n * (A + n * log 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simp only [A]; linarith
    _ = A / 2 * (1 / 2) ^ n + log 2 / 2 * ((n : ℝ) * (1 / 2) ^ n) := by ring

end LeanErgodicity
