import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.LeftRightNhds

/-!
# Ruin

In Lean `Real.log 0 = 0`, a junk value, so "the expected log of wealth is `-∞` when wealth can hit
zero" cannot be stated by plugging in zero. The honest statement is a limit: if an outcome has
probability `p > 0` and leaves wealth `x`, then as `x` approaches zero the expected log growth goes
to `-∞`, whatever the other outcomes are worth (`expected_log_tendsto_atBot`). No finite gain
elsewhere compensates for an outcome that can wipe you out.
-/

open Real Filter Topology

namespace LeanErgodicity

/-- As the worst outcome approaches zero, the expected log growth goes to `-∞`. Here `c` stands
for the contribution of every other outcome. -/
theorem expected_log_tendsto_atBot {p : ℝ} (hp : 0 < p) (c : ℝ) :
    Tendsto (fun x => p * log x + c) (𝓝[>] 0) atBot :=
  tendsto_atBot_add_const_right _ c (tendsto_log_nhdsGT_zero.const_mul_atBot hp)

/-- For every target growth rate `M`, a small enough worst outcome drags the expected log growth
below `M`. -/
theorem exists_ruinous_outcome {p : ℝ} (hp : 0 < p) (c M : ℝ) :
    ∃ ε > 0, ∀ x, 0 < x → x < ε → p * log x + c < M := by
  have h := (expected_log_tendsto_atBot hp c).eventually (eventually_lt_atBot M)
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h
  exact ⟨ε, hε, fun x hx0 hxε => hsub ⟨hx0, hxε⟩⟩

end LeanErgodicity
