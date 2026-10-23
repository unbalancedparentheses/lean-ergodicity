import LeanErgodicity.TimeAverage
import LeanErgodicity.Coin
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi

/-!
# The coin, almost surely

The 1.5 / 0.6 coin on an actual probability space: infinite sequences of fair coin flips,
`ℕ → Bool` with the product measure. Round `i` multiplies wealth by `3/2` if flip `i` is heads
and by `3/5` if it is tails.

* `coin_ae_wealth_tendsto_zero`: with probability one, a player who bets everything every round
  ends up with nothing, even though each round has an expected gain of 5% and expected wealth
  `(21/20)^n` grows without bound (`coin_expected_wealth`, `coin_expected_wealth_tendsto`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Real Finset
open scoped ENNReal

namespace LeanErgodicity

/-- A fair coin: heads (`true`) and tails (`false`) each with probability one half. -/
noncomputable def fairCoin : Measure Bool := (2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure fairCoin := by
  constructor
  simp only [fairCoin, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply_of_mem,
    Set.mem_univ, smul_eq_mul]
  rw [← two_mul, ← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

/-- Infinitely many independent fair coin flips. -/
noncomputable def coinFlips : Measure (ℕ → Bool) := Measure.infinitePi (fun _ => fairCoin)

instance : IsProbabilityMeasure coinFlips := by
  unfold coinFlips; infer_instance

/-- The growth factor of one flip. -/
noncomputable def coinFactorOf (b : Bool) : ℝ := if b then 3 / 2 else 3 / 5

/-- The growth factor in round `i`. -/
noncomputable def coinFactor (i : ℕ) (ω : ℕ → Bool) : ℝ := coinFactorOf (ω i)

theorem coinFactorOf_pos (b : Bool) : 0 < coinFactorOf b := by
  cases b <;> norm_num [coinFactorOf]

theorem measurable_coinFactorOf : Measurable coinFactorOf := measurable_of_finite _

theorem integral_fairCoin (g : Bool → ℝ) : ∫ b, g b ∂fairCoin = 1 / 2 * g true + 1 / 2 * g false := by
  rw [fairCoin, integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
    (integrable_dirac (by simp)), integral_dirac, integral_dirac]
  simp
  ring

theorem coinFlips_map_eval (i : ℕ) : coinFlips.map (fun ω => ω i) = fairCoin :=
  Measure.infinitePi_map_eval _ i

theorem integral_coinFlips_eval (i : ℕ) (g : Bool → ℝ) :
    ∫ ω, g (ω i) ∂coinFlips = 1 / 2 * g true + 1 / 2 * g false := by
  rw [← integral_fairCoin, ← coinFlips_map_eval i,
    integral_map (measurable_pi_apply i).aemeasurable (measurable_of_finite g).aestronglyMeasurable]

/-- **Almost every player goes broke.** With probability one, wealth goes to zero. -/
theorem coin_ae_wealth_tendsto_zero :
    ∀ᵐ ω ∂coinFlips, Tendsto (fun n : ℕ => ∏ i ∈ range n, coinFactor i ω) atTop (𝓝 0) := by
  have hmeas : ∀ i, Measurable (fun ω : ℕ → Bool => coinFactorOf (ω i)) := fun i =>
    measurable_coinFactorOf.comp (measurable_pi_apply i)
  have hindep : iIndepFun (fun i (ω : ℕ → Bool) => coinFactorOf (ω i)) coinFlips :=
    iIndepFun_infinitePi (P := fun _ => fairCoin) (X := fun _ => coinFactorOf)
      (fun _ => measurable_coinFactorOf)
  have hident : ∀ i, IdentDistrib (coinFactor i) (coinFactor 0) coinFlips coinFlips := by
    intro i
    refine ⟨(hmeas i).aemeasurable, (hmeas 0).aemeasurable, ?_⟩
    have hmap : ∀ j, coinFlips.map (coinFactor j) = fairCoin.map coinFactorOf := by
      intro j
      have : coinFactor j = coinFactorOf ∘ (fun ω : ℕ → Bool => ω j) := rfl
      rw [this, ← Measure.map_map measurable_coinFactorOf (measurable_pi_apply j),
        coinFlips_map_eval]
    rw [hmap, hmap]
  have hbound : ∀ b, |log (coinFactorOf b)| ≤ 1 := by
    intro b
    cases b
    · simp only [coinFactorOf, Bool.false_eq_true, ite_false]
      have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 5 by norm_num)
      have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 5 by norm_num)
      rw [abs_le]; constructor <;> norm_num at h1 h2 ⊢ <;> linarith
    · simp only [coinFactorOf, ite_true]
      have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
      have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
      rw [abs_le]; constructor <;> norm_num at h1 h2 ⊢ <;> linarith
  have hint : Integrable (fun ω => log (coinFactor 0 ω)) coinFlips := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      ((Real.measurable_log.comp (hmeas 0)).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs]; exact hbound (ω 0))
  have hneg : coinFlips[fun ω => log (coinFactor 0 ω)] < 0 := by
    have h := integral_coinFlips_eval 0 (fun b => log (coinFactorOf b))
    have e : (fun ω : ℕ → Bool => log (coinFactor 0 ω)) = fun ω => log (coinFactorOf (ω 0)) := rfl
    rw [e, h]
    simpa [coinFactorOf] using coin_time_average_neg
  exact ae_wealth_tendsto_zero coinFactor (fun i ω => coinFactorOf_pos (ω i)) hint
    (fun i j hij => hindep.indepFun hij) hident hneg

end LeanErgodicity
