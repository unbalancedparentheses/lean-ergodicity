import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The Kelly criterion for a two-outcome bet

A bet multiplies the stake by `1 + u` with probability `p` and by `1 - d` with probability `1 - p`.
Betting a fraction `f` of wealth gives the growth rate
`growth p u d f = p log (1 + u f) + (1 - p) log (1 - d f)`.

* `kelly_optimal`: the fraction `(p u - (1 - p) d) / (u d)` maximizes the growth rate over every
  fraction that cannot lose everything.
* `kelly_growth_pos`: when the bet has an edge, the optimal growth rate is strictly positive.
* `coin_kelly_fraction`, `coin_kelly_growth`: for the 1.5 / 0.6 coin the optimum is one quarter,
  and betting a quarter grows wealth while betting everything shrinks it.
-/

open Real

namespace LeanErgodicity

/-- Growth rate per round when betting a fraction `f` of wealth. -/
noncomputable def growth (p u d f : ℝ) : ℝ := p * log (1 + u * f) + (1 - p) * log (1 - d * f)

/-- The Kelly fraction. -/
noncomputable def kellyFraction (p u d : ℝ) : ℝ := (p * u - (1 - p) * d) / (u * d)

theorem one_add_kelly (p u d : ℝ) (hu : 0 < u) (hd : 0 < d) :
    1 + u * kellyFraction p u d = p * (u + d) / d := by
  unfold kellyFraction
  field_simp
  ring

theorem one_sub_kelly (p u d : ℝ) (hu : 0 < u) (hd : 0 < d) :
    1 - d * kellyFraction p u d = (1 - p) * (u + d) / u := by
  unfold kellyFraction
  field_simp
  ring

/-- **Kelly's criterion.** No fraction that keeps wealth positive grows faster than the Kelly
fraction. -/
theorem kelly_optimal {p u d f : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu : 0 < u) (hd : 0 < d)
    (hf1 : 0 < 1 + u * f) (hf2 : 0 < 1 - d * f) :
    growth p u d f ≤ growth p u d (kellyFraction p u d) := by
  have hq : 0 < 1 - p := by linarith
  have hud : 0 < u + d := by linarith
  have hA0 : 0 < p * (u + d) / d := by positivity
  have hB0 : 0 < (1 - p) * (u + d) / u := by positivity
  have hA := log_le_sub_one_of_pos (div_pos hf1 hA0)
  have hB := log_le_sub_one_of_pos (div_pos hf2 hB0)
  rw [log_div hf1.ne' hA0.ne'] at hA
  rw [log_div hf2.ne' hB0.ne'] at hB
  have key : p * ((1 + u * f) / (p * (u + d) / d) - 1) +
      (1 - p) * ((1 - d * f) / ((1 - p) * (u + d) / u) - 1) = 0 := by
    field_simp
    ring
  unfold growth
  rw [one_add_kelly p u d hu hd, one_sub_kelly p u d hu hd]
  nlinarith [mul_le_mul_of_nonneg_left hA hp0.le, mul_le_mul_of_nonneg_left hB hq.le]

/-- **A bet with an edge has positive optimal growth.** If `p u > (1 - p) d`, betting the Kelly
fraction grows wealth over time. -/
theorem kelly_growth_pos {p u d : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hu : 0 < u) (hd : 0 < d)
    (hedge : (1 - p) * d < p * u) :
    0 < growth p u d (kellyFraction p u d) := by
  have hq : 0 < 1 - p := by linarith
  have hud : 0 < u + d := by linarith
  have hA0 : 0 < p * (u + d) / d := by positivity
  have hB0 : 0 < (1 - p) * (u + d) / u := by positivity
  have hA1 : 1 / (p * (u + d) / d) ≠ 1 := by
    rw [ne_eq, div_eq_one_iff_eq hA0.ne']
    intro h
    have : p * (u + d) = d := by
      field_simp at h
      linarith
    nlinarith
  have hA := log_lt_sub_one_of_pos (by positivity) hA1
  have hB := log_le_sub_one_of_pos (show 0 < 1 / ((1 - p) * (u + d) / u) by positivity)
  rw [log_div one_ne_zero hA0.ne', log_one] at hA
  rw [log_div one_ne_zero hB0.ne', log_one] at hB
  have key : p * (1 / (p * (u + d) / d) - 1) + (1 - p) * (1 / ((1 - p) * (u + d) / u) - 1) = 0 := by
    field_simp
    ring
  unfold growth
  rw [one_add_kelly p u d hu hd, one_sub_kelly p u d hu hd]
  nlinarith [mul_lt_mul_of_pos_left hA hp0, mul_le_mul_of_nonneg_left hB hq.le]

/-- For the 1.5 / 0.6 coin (`u = 1/2`, `d = 2/5`), the Kelly fraction is one quarter. -/
theorem coin_kelly_fraction : kellyFraction (1 / 2) (1 / 2) (2 / 5) = 1 / 4 := by
  norm_num [kellyFraction]

/-- Betting a quarter of wealth on the coin grows at `½ log (81/80) > 0` per round. -/
theorem coin_kelly_growth : growth (1 / 2) (1 / 2) (2 / 5) (1 / 4) = 1 / 2 * log (81 / 80) := by
  unfold growth
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← mul_add, ← log_mul (by norm_num) (by norm_num)]
  norm_num

theorem coin_kelly_growth_pos : 0 < growth (1 / 2) (1 / 2) (2 / 5) (1 / 4) := by
  rw [coin_kelly_growth]
  have := log_pos (by norm_num : (1 : ℝ) < 81 / 80)
  linarith

/-- Betting everything on the coin shrinks wealth over time. -/
theorem coin_all_in_growth_neg : growth (1 / 2) (1 / 2) (2 / 5) 1 < 0 := by
  unfold growth
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← mul_add, ← log_mul (by norm_num) (by norm_num)]
  have := log_neg (by norm_num : (0 : ℝ) < (1 + 1 / 2 * 1) * (1 - 2 / 5 * 1)) (by norm_num)
  linarith

end LeanErgodicity
