import Mathlib.Probability.StrongLaw
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The time average along one trajectory

Ergodicity economics defines the growth rate a person experiences as a limit along a single
trajectory: `(1/n) log W_n`, where `W_n = G_0 ⋯ G_{n-1}` is wealth after `n` rounds and the `G_i`
are the per-round growth factors. This file proves that limit exists almost surely and equals
`E[log G]`, using Mathlib's strong law of large numbers (Etemadi's version, which only needs the
factors to be pairwise independent).

* `time_average_growth_ae`: almost surely, `(1/n) log W_n → E[log G]`. Increments of log wealth are
  the ergodic observable for multiplicative dynamics: their time average equals their expectation.
* `ae_wealth_tendsto_zero`: if `E[log G] < 0`, almost every trajectory goes to zero, even when
  `E[G] > 1` and expected wealth grows without bound.
* `ae_wealth_tendsto_atTop`: if `E[log G] > 0`, almost every trajectory grows without bound.
-/

open MeasureTheory ProbabilityTheory Filter Topology Real Finset

namespace LeanErgodicity

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The time-average growth rate.** Along almost every trajectory, `(1/n) log W_n` converges to
`E[log G]`. -/
theorem time_average_growth_ae (G : ℕ → Ω → ℝ) (hpos : ∀ i ω, 0 < G i ω)
    (hint : Integrable (fun ω => log (G 0 ω)) μ)
    (hindep : Pairwise (fun i j => IndepFun (G i) (G j) μ))
    (hident : ∀ i, IdentDistrib (G i) (G 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => log (∏ i ∈ range n, G i ω) / n) atTop
      (𝓝 (μ[fun ω => log (G 0 ω)])) := by
  have hX := strong_law_ae_real (fun i ω => log (G i ω)) hint
    (fun i j hij => (hindep hij).comp measurable_log measurable_log)
    (fun i => (hident i).comp measurable_log)
  filter_upwards [hX] with ω hω
  simpa [Real.log_prod (fun i _ => (hpos i ω).ne')] using hω

/-- A sequence whose average `a n / n` tends to a negative number tends to `-∞`. -/
theorem tendsto_atBot_of_div_tendsto_neg {a : ℕ → ℝ} {c : ℝ} (hc : c < 0)
    (h : Tendsto (fun n : ℕ => a n / n) atTop (𝓝 c)) : Tendsto a atTop atBot := by
  have hmul := h.neg_mul_atTop hc tendsto_natCast_atTop_atTop
  refine hmul.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

/-- A sequence whose average `a n / n` tends to a positive number tends to `+∞`. -/
theorem tendsto_atTop_of_div_tendsto_pos {a : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (h : Tendsto (fun n : ℕ => a n / n) atTop (𝓝 c)) : Tendsto a atTop atTop := by
  have hmul := h.pos_mul_atTop hc tendsto_natCast_atTop_atTop
  refine hmul.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  field_simp

/-- **Almost everyone goes broke.** If the expected log growth factor is negative, wealth tends to
zero along almost every trajectory. -/
theorem ae_wealth_tendsto_zero (G : ℕ → Ω → ℝ) (hpos : ∀ i ω, 0 < G i ω)
    (hint : Integrable (fun ω => log (G 0 ω)) μ)
    (hindep : Pairwise (fun i j => IndepFun (G i) (G j) μ))
    (hident : ∀ i, IdentDistrib (G i) (G 0) μ μ)
    (hneg : μ[fun ω => log (G 0 ω)] < 0) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => ∏ i ∈ range n, G i ω) atTop (𝓝 0) := by
  filter_upwards [time_average_growth_ae G hpos hint hindep hident] with ω hω
  have hlog := tendsto_atBot_of_div_tendsto_neg hneg hω
  have hexp := Real.tendsto_exp_atBot.comp hlog
  refine hexp.congr (fun n => ?_)
  simp only [Function.comp]
  exact Real.exp_log (prod_pos (fun i _ => hpos i ω))

/-- If the expected log growth factor is positive, wealth grows without bound along almost every
trajectory. -/
theorem ae_wealth_tendsto_atTop (G : ℕ → Ω → ℝ) (hpos : ∀ i ω, 0 < G i ω)
    (hint : Integrable (fun ω => log (G 0 ω)) μ)
    (hindep : Pairwise (fun i j => IndepFun (G i) (G j) μ))
    (hident : ∀ i, IdentDistrib (G i) (G 0) μ μ)
    (hpos' : 0 < μ[fun ω => log (G 0 ω)]) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => ∏ i ∈ range n, G i ω) atTop atTop := by
  filter_upwards [time_average_growth_ae G hpos hint hindep hident] with ω hω
  have hlog := tendsto_atTop_of_div_tendsto_pos hpos' hω
  have hexp := Real.tendsto_exp_atTop.comp hlog
  refine hexp.congr (fun n => ?_)
  simp only [Function.comp]
  exact Real.exp_log (prod_pos (fun i _ => hpos i ω))

end LeanErgodicity
