import NLS.ZakharovShabat.L2WholeLineNonrealResolvent
import NLS.FunctionalAnalysis.SymmetricPencilSurjective

/-! # Bounded physical right inverses give real whole-line resolvents -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
open NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- A bounded physical solution operator for a real parameter gives both
inverse identities on the actual closure domain. Symmetry supplies injectivity. -/
theorem mem_wholeLineResolventSet_of_bounded_AC_rightInverse (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) (hz : z.im = 0)
    (R : WholeLineL2 →L[ℂ] WholeLineL2)
    (hR : ∀ g : WholeLineL2, ∃ F : ℝ → ℂ × ℂ, wholeLineL2Pair (R g) =ᵐ[volume] F ∧
      (∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b) ∧
      physicalOperator (l2WholeLinePotential u) F =ᵐ[volume]
        (fun t => z • F t-wholeLineL2Pair g t)) :
    z ∈ wholeLineResolventSet u := by
  have hAC (g : WholeLineL2) : ∃ F : ℝ → ℂ × ℂ,
      wholeLineL2Pair (R g) =ᵐ[volume] F ∧
      (∀ a b : ℝ, AbsolutelyContinuousOnInterval F a b) ∧
      physicalOperator (l2WholeLinePotential u) F =ᵐ[volume] wholeLineL2Pair (z • R g-g) := by
    obtain ⟨F,he,hac,hp⟩ := hR g
    refine ⟨F,he,hac,?_⟩
    filter_upwards [hp,he,Lp.coeFn_sub (z • R g) g,Lp.coeFn_smul z (R g)]
      with t hpt het hsub hsm
    rw [hpt]
    change z • F t-WithLp.ofLp (g t) = WithLp.ofLp ((z • R g-g) t)
    simp only [Pi.sub_apply,Pi.smul_apply] at hsub hsm
    rw [hsub,hsm]
    change z • F t-wholeLineL2Pair g t = z • wholeLineL2Pair (R g) t-wholeLineL2Pair g t
    rw [het]
  have hdom (g : WholeLineL2) : R g ∈ (wholeLineMinimalOperator u).closure.domain := by
    obtain ⟨F,he,hac,hp⟩ := hAC g
    exact (mem_wholeLineMinimalOperator_closure_domain_iff_AC u hu (R g)).mpr
      ⟨F,z • R g-g,he,hac,hp⟩
  have himg (g : WholeLineL2) :
      (wholeLineMinimalOperator u).closure ⟨R g,hdom g⟩ = z • R g-g := by
    obtain ⟨F,he,hac,hp⟩ := hAC g
    have h := wholeLineMinimalOperator_adjoint_eq_of_AC_representative
      u hu (R g) (z • R g-g) F he hac hp
    exact ((le_of_eq (wholeLineMinimalOperator_closure_eq_adjoint u hu)).2 rfl).trans h
  let S : WholeLineL2 →L[ℂ] (wholeLineMinimalOperator u).closure.domain :=
    R.codRestrict _ hdom
  have hright (g : WholeLineL2) : wholeLinePencil u z (S g) = g := by
    change z • R g-(wholeLineMinimalOperator u).closure ⟨R g,hdom g⟩ = g
    rw [himg]
    module
  have hT := wholeLineMinimalOperator_closure_isSelfAdjoint u hu
  have hs : (wholeLineMinimalOperator u).closure.IsFormalAdjoint
      (wholeLineMinimalOperator u).closure := by
    simpa only [LinearPMap.isSelfAdjoint_def.mp hT] using
      LinearPMap.adjoint_isFormalAdjoint hT.dense_domain
  have hinj : Function.Injective (wholeLinePencil u z) :=
    linearPMapPencil_injective_of_surjective_real _ hs z hz
      (fun g => ⟨S g,hright g⟩)
  exact ⟨S,hright,fun f => hinj (hright (wholeLinePencil u z f))⟩

end NLS.ZakharovShabat
