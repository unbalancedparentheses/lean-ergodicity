import LeanErgodicity.Jensen
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Time averages and ensemble averages

A bet multiplies wealth by `x i > 0` in outcome `i` of a finite type `ι`, with probabilities `w`.
It is repeated `n` times independently, so a history is a function `ω : Fin n → ι`, with probability
`∏ k, w (ω k)` and final wealth `∏ k, x (ω k)`.

* `expected_wealth_eq`: expected final wealth is `(E x)^n`. The average across players compounds at
  `log (E x)` per round.
* `expected_log_wealth_eq`: the expected log of final wealth is `n · E[log x]`. One player compounds
  at `E[log x]` per round.
* `time_average_lt_ensemble`: whenever the bet is not a sure thing, `E[log x] < log (E x)`. The two
  averages differ, which is what it means for wealth not to be ergodic.
-/

open Real Finset

namespace LeanErgodicity

variable {ι : Type*} [Fintype ι]

/-- Expected wealth after `n` independent rounds is the expected factor to the power `n`. -/
theorem expected_wealth_eq (w x : ι → ℝ) (n : ℕ) :
    ∑ ω : Fin n → ι, (∏ k, w (ω k)) * ∏ k, x (ω k) = (∑ i, w i * x i) ^ n := by
  rw [← Fin.prod_const, Finset.prod_univ_sum]
  simp [Fintype.piFinset_univ, Finset.prod_mul_distrib]

/-- The probability of one round's outcome, with every other round summed out. -/
theorem sum_prod_weights_mul (w f : ι → ℝ) (hsum : ∑ i, w i = 1) (n : ℕ) (j : Fin n) :
    ∑ ω : Fin n → ι, (∏ k, w (ω k)) * f (ω j) = ∑ i, w i * f i := by
  have h := Finset.prod_univ_sum (fun _ : Fin n => (univ : Finset ι))
    (fun k i => w i * if k = j then f i else 1)
  simp only [Fintype.piFinset_univ] at h
  have lhs : ∀ ω : Fin n → ι,
      (∏ k, w (ω k) * if k = j then f (ω k) else 1) = (∏ k, w (ω k)) * f (ω j) := by
    intro ω
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' univ j (fun k => f (ω k))]
    simp
  have rhs : (∏ k : Fin n, ∑ i, w i * if k = j then f i else 1) = ∑ i, w i * f i := by
    rw [Finset.prod_eq_single j]
    · simp
    · intro k _ hk
      simp [hk, hsum]
    · simp
  simp_rw [lhs] at h
  rw [← h, rhs]

/-- The expected log of final wealth is `n` times the expected log of one round's factor. -/
theorem expected_log_wealth_eq (w x : ι → ℝ) (hsum : ∑ i, w i = 1) (hx : ∀ i, 0 < x i)
    (n : ℕ) :
    ∑ ω : Fin n → ι, (∏ k, w (ω k)) * log (∏ k, x (ω k)) = n * ∑ i, w i * log (x i) := by
  have hlog : ∀ ω : Fin n → ι, log (∏ k, x (ω k)) = ∑ k, log (x (ω k)) := fun ω =>
    Real.log_prod (fun k _ => (hx (ω k)).ne')
  simp_rw [hlog, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [sum_prod_weights_mul w (fun i => log (x i)) hsum n]
  simp [Finset.mul_sum]

/-- **Wealth is not ergodic.** If a bet can multiply wealth by two different factors, each with
positive probability, then the growth rate one player experiences over time is strictly below the
growth rate of the average across players. -/
theorem time_average_lt_ensemble (w x : ι → ℝ) (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hx : ∀ i, 0 < x i) {j k : ι} (hjk : x j ≠ x k) :
    ∑ i, w i * log (x i) < log (∑ i, w i * x i) :=
  (expected_log_lt_log_expected_iff univ w x (fun i _ => hw i) hsum (fun i _ => hx i)).mpr
    ⟨j, mem_univ _, k, mem_univ _, hjk⟩

end LeanErgodicity
