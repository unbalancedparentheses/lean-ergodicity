import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Insurance can make both sides grow faster

The example from Peters and Adamou's "Insurance makes wealth grow faster", in its smallest form.
An owner with wealth 2 faces a loss of 1 with probability one half. An insurer with wealth 10 can
take that risk for a fee `F`.

* Measured by expected wealth, insurance is zero-sum: whatever the owner loses on average, the
  insurer gains (`insurance_expected_zero_sum`). No fee helps both.
* Measured by the time-average growth rate, the owner gains exactly when `(2 - F)² > 2`
  (`owner_gains_iff`) and the insurer exactly when `(9 + F)(10 + F) > 100` (`insurer_gains_iff`).
* Every fee from 0.513 to 0.585 satisfies both (`insurance_win_win`), even though every such fee is
  above the expected loss of 0.5, so the insurer also profits on average.
-/

open Real

namespace LeanErgodicity

/-- The owner's growth rate without insurance: wealth 2, or 1 after the loss. -/
noncomputable def ownerUninsured : ℝ := 1 / 2 * log 2 + 1 / 2 * log 1

/-- The owner's growth rate after paying the fee `F`: wealth `2 - F` for sure. -/
noncomputable def ownerInsured (F : ℝ) : ℝ := log (2 - F)

/-- The insurer's growth rate after selling the policy: it collects `F` and pays 1 half the time. -/
noncomputable def insurerInsured (F : ℝ) : ℝ := 1 / 2 * log (10 + F - 1) + 1 / 2 * log (10 + F)

/-- The insurer's growth rate without the policy. -/
noncomputable def insurerUninsured : ℝ := log 10

/-- In expected wealth, the owner's change and the insurer's change sum to zero for every fee. -/
theorem insurance_expected_zero_sum (F : ℝ) :
    ((2 - F) - (1 / 2 * 2 + 1 / 2 * 1)) + ((1 / 2 * (10 + F - 1) + 1 / 2 * (10 + F)) - 10) = 0 := by
  ring

theorem owner_gains_iff {F : ℝ} (hF : F < 2) :
    ownerUninsured < ownerInsured F ↔ 2 < (2 - F) ^ 2 := by
  have h2F : 0 < 2 - F := by linarith
  unfold ownerUninsured ownerInsured
  rw [log_one, mul_zero, add_zero]
  constructor
  · intro h
    have : log 2 < log ((2 - F) ^ 2) := by rw [log_pow]; push_cast; linarith
    exact (log_lt_log_iff (by norm_num) (by positivity)).mp this
  · intro h
    have := log_lt_log (by norm_num) h
    rw [log_pow] at this
    push_cast at this
    linarith

theorem insurer_gains_iff {F : ℝ} (hF : 0 ≤ F) :
    insurerUninsured < insurerInsured F ↔ 100 < (9 + F) * (10 + F) := by
  have h9 : 0 < 9 + F := by linarith
  have h10 : 0 < 10 + F := by linarith
  unfold insurerUninsured insurerInsured
  rw [show (10 : ℝ) + F - 1 = 9 + F by ring, ← mul_add, ← log_mul h9.ne' h10.ne']
  have h100 : log 10 = 1 / 2 * log 100 := by
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num, log_pow]; push_cast; ring
  rw [h100]
  constructor
  · intro h
    exact (log_lt_log_iff (by norm_num) (by positivity)).mp (by linarith)
  · intro h
    have := log_lt_log (by norm_num) h
    linarith

/-- **Insurance is win-win in growth.** Every fee between 0.513 and 0.585 raises the time-average
growth rate of both the owner and the insurer. -/
theorem insurance_win_win {F : ℝ} (hlo : 513 / 1000 ≤ F) (hhi : F ≤ 585 / 1000) :
    ownerUninsured < ownerInsured F ∧ insurerUninsured < insurerInsured F := by
  constructor
  · rw [owner_gains_iff (by linarith)]
    nlinarith
  · rw [insurer_gains_iff (by linarith)]
    nlinarith

/-- Every win-win fee is above the expected loss, so the insurer also profits on average. -/
theorem win_win_fee_exceeds_expected_loss {F : ℝ} (hlo : 513 / 1000 ≤ F) : 1 / 2 * 1 < F := by
  linarith

end LeanErgodicity
