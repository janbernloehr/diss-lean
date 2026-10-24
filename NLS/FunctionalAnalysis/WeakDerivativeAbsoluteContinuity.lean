import NLS.FunctionalAnalysis.WeakDerivativeConstant
import NLS.FunctionalAnalysis.LocallyIntegrablePrimitive

/-! # Absolutely continuous representatives of weakly differentiable functions -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped ContDiff
namespace NLS.FunctionalAnalysis

/-- A locally integrable function with a locally integrable weak derivative
has a representative absolutely continuous on every finite interval. The
same representative has the prescribed classical derivative almost everywhere. -/
theorem exists_locally_absolutelyContinuous_of_weak_derivative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f g : ℝ → E) (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (hw : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ t : ℝ, deriv ψ t • f t + ψ t • g t) = 0) :
    ∃ F : ℝ → E, f =ᵐ[volume] F ∧
      (∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b) ∧
      ∀ᵐ t : ℝ, HasDerivAt F (g t) t := by
  let G : ℝ → E := fun t => ∫ s in (0 : ℝ)..t, g s
  have hG : Continuous G := continuous_local_primitive hg 0
  have hGl : LocallyIntegrable G volume := hG.locallyIntegrable
  have hk : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ t : ℝ, deriv ψ t • (f t-G t)) = 0 := by
    intro ψ hψ hc
    have hdψ := hψ.continuous_deriv (by norm_num)
    have hi1 := hf.integrable_smul_left_of_hasCompactSupport hdψ hc.deriv
    have hi2 := hGl.integrable_smul_left_of_hasCompactSupport hdψ hc.deriv
    have hi3 := hg.integrable_smul_left_of_hasCompactSupport hψ.continuous hc
    have h1 := hw ψ hψ hc
    have h2 := integral_deriv_smul_local_primitive_eq_zero hg 0 ψ hψ hc
    change (∫ t : ℝ, deriv ψ t • G t + ψ t • g t) = 0 at h2
    rw [integral_add hi1 hi3] at h1
    rw [integral_add hi2 hi3] at h2
    simp only [smul_sub]
    rw [integral_sub hi1 hi2,sub_eq_zero]
    exact add_right_cancel (h1.trans h2.symm)
  obtain ⟨v,hv⟩ := ae_eq_const_of_integral_deriv_smul_eq_zero
    (fun t => f t-G t) (hf.sub hGl) hk
  refine ⟨fun t => v+G t,?_,?_,?_⟩
  · filter_upwards [hv] with t ht
    exact sub_eq_iff_eq_add.mp ht
  · intro a b
    exact absolutelyContinuousOnInterval_const_add
      (absolutelyContinuousOnInterval_local_primitive hg 0 a b) v
  · filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hg] with t ht
    exact (ht 0).const_add v

end NLS.FunctionalAnalysis
