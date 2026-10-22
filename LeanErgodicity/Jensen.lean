import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Jensen's inequality for the logarithm, and volatility drag

A finite distribution is a finset `s` of outcomes with weights `w` that are nonnegative and sum to
one. Wealth is multiplied by a positive factor `x i` in outcome `i`.

* `expected_log_le_log_expected`: the expected log of the factor is at most the log of the expected
  factor. The left side is the growth rate one investor compounds at over time; the right side is
  the growth rate of the average across investors.
* `expected_log_lt_log_expected_iff`: the inequality is strict exactly when the factor varies.
* `growth_le_log_one_add_mean`: the same statement written with returns, `x = 1 + R`.
* `volatility_drag`: the growth rate is `μ - σ²/2 - μ²/2` up to an explicit third-order error.
-/

open Real Finset

namespace LeanErgodicity

variable {ι : Type*}

/-- **Jensen's inequality for the logarithm.** The expected log growth factor is at most the log of
the expected growth factor. -/
theorem expected_log_le_log_expected (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1) (hx : ∀ i ∈ s, 0 < x i) :
    ∑ i ∈ s, w i * log (x i) ≤ log (∑ i ∈ s, w i * x i) := by
  simpa [smul_eq_mul] using
    strictConcaveOn_log_Ioi.concaveOn.le_map_sum hw hsum (fun i hi => Set.mem_Ioi.mpr (hx i hi))

/-- The gap in Jensen's inequality is strictly positive exactly when the growth factor takes two
different values with positive probability. -/
theorem expected_log_lt_log_expected_iff (s : Finset ι) (w x : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (hsum : ∑ i ∈ s, w i = 1) (hx : ∀ i ∈ s, 0 < x i) :
    ∑ i ∈ s, w i * log (x i) < log (∑ i ∈ s, w i * x i) ↔ ∃ j ∈ s, ∃ k ∈ s, x j ≠ x k := by
  simpa [smul_eq_mul] using
    strictConcaveOn_log_Ioi.lt_map_sum_iff_of_pos hw hsum (fun i hi => Set.mem_Ioi.mpr (hx i hi))

/-- Jensen's inequality written with returns: the compound growth rate `E[log (1 + R)]` is at most
`log (1 + E[R])`, the growth rate implied by the average return. -/
theorem growth_le_log_one_add_mean (s : Finset ι) (w R : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1) (hR : ∀ i ∈ s, -1 < R i) :
    ∑ i ∈ s, w i * log (1 + R i) ≤ log (1 + ∑ i ∈ s, w i * R i) := by
  have h := expected_log_le_log_expected s w (fun i => 1 + R i) hw hsum
    (fun i hi => by linarith [hR i hi])
  have hmean : ∑ i ∈ s, w i * (1 + R i) = 1 + ∑ i ∈ s, w i * R i := by
    simp [mul_add, sum_add_distrib, hsum]
  simpa [hmean] using h

/-- Second-order expansion of `log (1 + r)` with an explicit remainder. -/
theorem abs_log_one_add_sub_quadratic_le {r : ℝ} (h : |r| < 1) :
    |log (1 + r) - (r - r ^ 2 / 2)| ≤ |r| ^ 3 / (1 - |r|) := by
  have key := Real.abs_log_sub_add_sum_range_le (x := -r) (by rwa [abs_neg]) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, sub_neg_eq_add] at key
  convert key using 2
  ring

/-- The mean of `R` under the weights `w`. -/
noncomputable def mean (s : Finset ι) (w R : ι → ℝ) : ℝ := ∑ i ∈ s, w i * R i

/-- The variance of `R` under the weights `w`. -/
noncomputable def variance (s : Finset ι) (w R : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * (R i - mean s w R) ^ 2

/-- The second moment is the variance plus the squared mean. -/
theorem second_moment_eq_variance_add (s : Finset ι) (w R : ι → ℝ) (hsum : ∑ i ∈ s, w i = 1) :
    ∑ i ∈ s, w i * R i ^ 2 = variance s w R + mean s w R ^ 2 := by
  unfold variance
  set μ := mean s w R with hμ
  have h : ∑ i ∈ s, w i * (R i - μ) ^ 2 =
      ∑ i ∈ s, (w i * R i ^ 2 - 2 * μ * (w i * R i) + μ ^ 2 * w i) :=
    sum_congr rfl (fun i _ => by ring)
  rw [h, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, hsum]
  have : ∑ i ∈ s, w i * R i = μ := rfl
  rw [this]
  ring

/-- **Volatility drag.** For returns smaller than 100% in absolute value, the compound growth rate
`E[log (1 + R)]` equals `μ - σ²/2 - μ²/2` up to an error bounded by `E[|R|³ / (1 - |R|)]`, where `μ`
is the mean return and `σ²` its variance. For small returns this is the familiar `μ - σ²/2`. -/
theorem volatility_drag (s : Finset ι) (w R : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1) (hR : ∀ i ∈ s, |R i| < 1) :
    |∑ i ∈ s, w i * log (1 + R i) -
        (mean s w R - variance s w R / 2 - mean s w R ^ 2 / 2)| ≤
      ∑ i ∈ s, w i * (|R i| ^ 3 / (1 - |R i|)) := by
  have hm := second_moment_eq_variance_add s w R hsum
  have hrw : mean s w R - variance s w R / 2 - mean s w R ^ 2 / 2 =
      ∑ i ∈ s, w i * (R i - R i ^ 2 / 2) := by
    have h : ∑ i ∈ s, w i * (R i - R i ^ 2 / 2) =
        ∑ i ∈ s, w i * R i - (∑ i ∈ s, w i * R i ^ 2) * (1 / 2) := by
      rw [sum_mul, ← sum_sub_distrib]
      exact sum_congr rfl (fun i _ => by ring)
    rw [h, hm]
    unfold mean
    ring
  rw [hrw, ← sum_sub_distrib]
  calc |∑ i ∈ s, (w i * log (1 + R i) - w i * (R i - R i ^ 2 / 2))|
      ≤ ∑ i ∈ s, |w i * log (1 + R i) - w i * (R i - R i ^ 2 / 2)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, w i * (|R i| ^ 3 / (1 - |R i|)) := by
      apply sum_le_sum
      intro i hi
      rw [← mul_sub, abs_mul, abs_of_nonneg (hw i hi)]
      exact mul_le_mul_of_nonneg_left (abs_log_one_add_sub_quadratic_le (hR i hi)) (hw i hi)

end LeanErgodicity
