import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Losses and recoveries

* `recovery_gain`: after a loss of `L`, a gain of `L / (1 - L)` restores the starting wealth, and
  it is the only gain that does (`recovery_gain_unique`).
* `loss_lt_recovery_gain`: the gain needed is always larger than the loss.
* `up_then_down`: a gain of `x` followed by a loss of `x` leaves wealth below where it started.
* `dow_1929_recovery`: the Dow's 89% loss from 1929 to 1932 needed a gain of more than 800%.
-/

namespace LeanErgodicity

/-- A loss of `L` followed by a gain of `L / (1 - L)` returns wealth to where it started. -/
theorem recovery_gain {L : ℝ} (hL : L < 1) : (1 - L) * (1 + L / (1 - L)) = 1 := by
  have : (1 - L) ≠ 0 := by linarith
  field_simp
  ring

/-- `L / (1 - L)` is the only gain that recovers a loss of `L`. -/
theorem recovery_gain_unique {L g : ℝ} (hL : L < 1) (h : (1 - L) * (1 + g) = 1) :
    g = L / (1 - L) := by
  have : (1 - L) ≠ 0 := by linarith
  field_simp
  linarith

/-- Recovering from a loss takes a strictly larger gain than the loss. -/
theorem loss_lt_recovery_gain {L : ℝ} (hL0 : 0 < L) (hL1 : L < 1) : L < L / (1 - L) := by
  rw [lt_div_iff₀ (by linarith)]
  nlinarith

/-- A gain of `x` followed by a loss of `x` (or the reverse) loses money whenever `x ≠ 0`. -/
theorem up_then_down {x : ℝ} (hx : x ≠ 0) : (1 + x) * (1 - x) < 1 := by
  nlinarith [sq_pos_of_ne_zero hx]

/-- \$100 that gains 50% and then loses 50% ends at \$75. -/
theorem up_fifty_down_fifty : (100 : ℝ) * (3 / 2) * (1 / 2) = 75 := by norm_num

/-- The Dow lost about 89% from September 1929 to July 1932; recovering needed a gain above 800%. -/
theorem dow_1929_recovery : 8 < (89 / 100 : ℝ) / (1 - 89 / 100) := by norm_num

end LeanErgodicity
