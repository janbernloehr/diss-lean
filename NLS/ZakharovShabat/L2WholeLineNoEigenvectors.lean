import NLS.ZakharovShabat.L2WholeLineACUniqueness
import NLS.ZakharovShabat.L2WholeLineNoL2Solution
import NLS.ZakharovShabat.L2WholeLineClosureRepresentative

/-! # The original self-adjoint whole-line operator has no eigenvectors -/
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace NLS.ZakharovShabat

/-- A vector in the actual closure domain satisfying the physical eigenvalue
equation must be zero, at every complex parameter including band endpoints. -/
theorem wholeLineMinimalOperator_closure_eigenvector_eq_zero (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ)
    (f : (wholeLineMinimalOperator u).closure.domain)
    (hf : (wholeLineMinimalOperator u).closure f = z • (f : WholeLineL2)) :
    (f : WholeLineL2) = 0 := by
  obtain ⟨F,he,hac,hd⟩ := wholeLineMinimalOperator_closure_exists_AC_representative u hu f
  have hG : wholeLineL2Pair ((wholeLineMinimalOperator u).closure f) =ᵐ[volume]
      (fun t => z • F t) := by
    rw [hf]
    filter_upwards [Lp.coeFn_smul z (f : WholeLineL2),he] with t hsm het
    change WithLp.ofLp ((z • (f : WholeLineL2)) t) = _
    rw [hsm]
    change z • wholeLineL2Pair f t = z • F t
    rw [het]
  have hode : ∀ᵐ t : ℝ, HasDerivAt F
      (classicalODECoefficient (l2WholeLinePotential u t) z (F t)) t := by
    filter_upwards [hd,he,hG] with t hdt het hGt
    convert! hdt using 1
    dsimp only [wholeLineWeakDerivative]
    rw [hGt,het]
    simp [mul_assoc]
  have hsol := l2WholeLineSolution_unique_AC u z F hac hode
  have hm : MemLp F 2 volume := (memLp_wholeLineL2Pair f).ae_eq he
  have hv : ![(F 0).1,(F 0).2] = (0 : Fin 2 → ℂ) := by
    by_contra hn
    rw [hsol] at hm
    exact not_memLp_l2WholeLineSolution u z _ hn hm
  have hzF : F = 0 := by
    rw [hsol,hv]
    funext t
    simp [l2WholeLineSolution]
  apply Lp.ext
  filter_upwards [he,Lp.coeFn_zero (E := WholeLineVector) (p := 2) (μ := volume)] with t het hzero
  rw [hzero]
  apply (WithLp.linearEquiv 2 ℂ (ℂ × ℂ)).injective
  change wholeLineL2Pair f t = 0
  rw [het,hzF]
  rfl

/-- No complex number has a nonzero eigenvector in the actual physical domain. -/
theorem wholeLineMinimalOperator_closure_no_eigenvectors (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (z : ℂ) :
    ¬ ∃ f : (wholeLineMinimalOperator u).closure.domain,
      (f : WholeLineL2) ≠ 0 ∧ (wholeLineMinimalOperator u).closure f = z • (f : WholeLineL2) := by
  rintro ⟨f,hf0,hf⟩
  exact hf0 (wholeLineMinimalOperator_closure_eigenvector_eq_zero u hu z f hf)

/-- Absence of physical eigenvectors applies to the unchanged original real source. -/
theorem source_wholeLineMinimalOperator_closure_no_eigenvectors (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (z : ℂ) :
    ¬ ∃ f : (wholeLineMinimalOperator (sourcePhysicalL2 φ)).closure.domain,
      (f : WholeLineL2) ≠ 0 ∧ (wholeLineMinimalOperator (sourcePhysicalL2 φ)).closure f =
        z • (f : WholeLineL2) :=
  wholeLineMinimalOperator_closure_no_eigenvectors _ ((sourcePhysicalL2_realType_iff φ).mpr hφ) z

end NLS.ZakharovShabat
