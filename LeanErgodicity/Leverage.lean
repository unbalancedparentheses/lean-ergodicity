import Mathlib.Tactic

/-!
# Optimal leverage

For an asset whose price follows geometric Brownian motion with drift `μ` and volatility `σ`,
and a risk-free rate `r`, an investor who holds a constant leverage `l` (the fraction of wealth in
the asset, borrowing or lending the rest at `r`) has the time-average growth rate

  `g(l) = r + l (μ - r) - l² σ² / 2`

(Peters 2011, "Optimal leverage from non-ergodicity", Eq. 22). Deriving this formula takes Itô's
lemma, which Mathlib does not have yet, so here it is the definition, and everything below is
proved from it.

* `leverage_optimal`: the Kelly leverage `l* = (μ - r) / σ²` maximizes `g`.
* `growth_at_kelly`: at `l*`, growth is `r + (μ - r)² / (2σ²)`.
* `growth_at_twice_kelly`: at `2 l*`, growth falls back to exactly `r`.
* `growth_fractional_kelly`: at `c · l*`, the excess growth over `r` is `c (2 - c)` times the
  maximum. Half Kelly keeps exactly three quarters (`growth_half_kelly`).
* `growth_below_riskfree_iff`: leverage beyond `2 l*` grows slower than holding cash.
-/

namespace LeanErgodicity

/-- Time-average growth rate at leverage `l`. -/
noncomputable def levGrowth (r μ σ l : ℝ) : ℝ := r + l * (μ - r) - l ^ 2 * σ ^ 2 / 2

/-- The Kelly leverage. -/
noncomputable def kellyLeverage (r μ σ : ℝ) : ℝ := (μ - r) / σ ^ 2

/-- Growth at any leverage, written around the Kelly leverage. -/
theorem levGrowth_eq {r μ σ : ℝ} (hσ : σ ≠ 0) (l : ℝ) :
    levGrowth r μ σ l =
      r + (μ - r) ^ 2 / (2 * σ ^ 2) - σ ^ 2 / 2 * (l - kellyLeverage r μ σ) ^ 2 := by
  unfold levGrowth kellyLeverage
  field_simp
  ring

/-- **Optimal leverage.** No leverage grows faster than `(μ - r) / σ²`. -/
theorem leverage_optimal {r μ σ : ℝ} (hσ : σ ≠ 0) (l : ℝ) :
    levGrowth r μ σ l ≤ levGrowth r μ σ (kellyLeverage r μ σ) := by
  rw [levGrowth_eq hσ l, levGrowth_eq hσ (kellyLeverage r μ σ)]
  nlinarith [sq_nonneg (l - kellyLeverage r μ σ), sq_nonneg σ]

theorem growth_at_kelly {r μ σ : ℝ} (hσ : σ ≠ 0) :
    levGrowth r μ σ (kellyLeverage r μ σ) = r + (μ - r) ^ 2 / (2 * σ ^ 2) := by
  rw [levGrowth_eq hσ]
  ring

/-- **Twice Kelly earns the risk-free rate.** -/
theorem growth_at_twice_kelly {r μ σ : ℝ} (hσ : σ ≠ 0) :
    levGrowth r μ σ (2 * kellyLeverage r μ σ) = r := by
  unfold levGrowth kellyLeverage
  field_simp
  ring

/-- At a fraction `c` of the Kelly leverage, the growth above the risk-free rate is `c (2 - c)`
times its maximum. -/
theorem growth_fractional_kelly {r μ σ : ℝ} (hσ : σ ≠ 0) (c : ℝ) :
    levGrowth r μ σ (c * kellyLeverage r μ σ) - r =
      c * (2 - c) * (levGrowth r μ σ (kellyLeverage r μ σ) - r) := by
  rw [growth_at_kelly hσ]
  unfold levGrowth kellyLeverage
  field_simp
  ring

/-- **Half Kelly keeps three quarters of the excess growth.** -/
theorem growth_half_kelly {r μ σ : ℝ} (hσ : σ ≠ 0) :
    levGrowth r μ σ (kellyLeverage r μ σ / 2) - r =
      3 / 4 * (levGrowth r μ σ (kellyLeverage r μ σ) - r) := by
  have h := growth_fractional_kelly hσ (1 / 2) (r := r) (μ := μ)
  rw [show (1 / 2 : ℝ) * kellyLeverage r μ σ = kellyLeverage r μ σ / 2 by ring] at h
  rw [h]
  ring

/-- **Too much leverage loses to cash.** With a positive excess return, leverage above twice
Kelly grows slower than the risk-free rate. -/
theorem growth_below_riskfree_of_gt_twice {r μ σ l : ℝ} (hσ : σ ≠ 0) (hμ : r < μ)
    (hl : 2 * kellyLeverage r μ σ < l) : levGrowth r μ σ l < r := by
  have hk : 0 < kellyLeverage r μ σ := by
    unfold kellyLeverage; exact div_pos (by linarith) (by positivity)
  have hσ2 : 0 < σ ^ 2 := by positivity
  rw [levGrowth_eq hσ]
  have hmr : (μ - r) ^ 2 / (2 * σ ^ 2) = σ ^ 2 / 2 * kellyLeverage r μ σ ^ 2 := by
    unfold kellyLeverage; field_simp
  rw [hmr]
  nlinarith [mul_pos hσ2 (show 0 < (l - kellyLeverage r μ σ) ^ 2 - kellyLeverage r μ σ ^ 2 by nlinarith)]

end LeanErgodicity
