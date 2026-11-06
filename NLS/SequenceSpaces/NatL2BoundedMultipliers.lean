import NLS.SequenceSpaces.NatL2AnalyticRealization

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal Classical

namespace NLS.Coeff



variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Bounded scalar multipliers preserve a summable complex square norm. -/
theorem summable_sq_mul_of_bounded (a b : ℕ → ℂ) (M : ℝ) (hM : 0≤M)
    (ha : Summable (fun k => ‖a k‖^2)) (hb : ∀ k, ‖b k‖≤M) :
    Summable (fun k => ‖a k*b k‖^2) ∧
      (∑' k, ‖a k*b k‖^2)≤(∑' k, ‖a k‖^2)*M^2 := by
  have hmajor : Summable (fun k => ‖a k‖^2*M^2) := ha.mul_right (M^2)
  have hbound (k : ℕ) : ‖a k*b k‖^2≤‖a k‖^2*M^2 := by
    rw [norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hM).mpr (hb k)) (sq_nonneg _)
  have hs : Summable (fun k => ‖a k*b k‖^2) := hmajor.of_nonneg_of_le (fun k => sq_nonneg _) hbound
  refine ⟨hs,?_⟩
  exact (hs.tsum_le_tsum hbound hmajor).trans_eq tsum_mul_right

/-- A uniformly bounded analytic diagonal multiplier preserves actual
Hilbert analyticity of a scalar analytic square-summable sequence. -/
theorem analyticOnNhd_natL2OfFunction_mul_of_uniform_bound
    (a b : E → ℕ → ℂ) (U : Set E) (hU : IsOpen U)
    (haa : ∀ k, AnalyticOnNhd ℂ (fun x => a x k) U)
    (hba : ∀ k, AnalyticOnNhd ℂ (fun x => b x k) U)
    (C M : ℝ) (hM : 0≤M)
    (ha : ∀ x∈U, Summable (fun k => ‖a x k‖^2) ∧ (∑' k, ‖a x k‖^2)≤C)
    (hb : ∀ x∈U, ∀ k, ‖b x k‖≤M) :
    AnalyticOnNhd ℂ (fun x => natL2OfFunction (fun k => a x k*b x k)) U ∧
      ∀ x∈U, ‖natL2OfFunction (fun k => a x k*b x k)‖^2≤C*M^2 ∧
        ∀ k, natL2OfFunction (fun k => a x k*b x k) (Equiv.intEquivNat.symm k)=a x k*b x k := by
  have hsq (x : E) (hx : x∈U) : Summable (fun k => ‖a x k*b x k‖^2) ∧
      (∑' k, ‖a x k*b x k‖^2)≤C*M^2 := by
    obtain ⟨hs,ht⟩ := summable_sq_mul_of_bounded (a x) (b x) M hM (ha x hx).1 (hb x hx)
    exact ⟨hs,ht.trans (mul_le_mul_of_nonneg_right (ha x hx).2 (sq_nonneg _))⟩
  refine ⟨analyticOnNhd_natL2OfFunction_of_summable_sq_bound _ U hU
    (fun k => (haa k).mul (hba k)) (C*M^2) hsq,?_⟩
  intro x hx
  exact ⟨(norm_natL2OfFunction_sq_eq_tsum _ (hsq x hx).1).le.trans (hsq x hx).2,
    natL2OfFunction_apply_of_summable_sq _ (hsq x hx).1⟩

end NLS.Coeff
