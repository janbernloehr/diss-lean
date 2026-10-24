import NLS.FunctionalAnalysis.SelfAdjointCayleyEigenvectors
import NLS.ZakharovShabat.L2WholeLineCayley
import NLS.ZakharovShabat.L2WholeLineNoEigenvectors

/-! # Absence of eigenvectors for the original physical Cayley transform -/
noncomputable section
set_option autoImplicit false
open NLS.FunctionalAnalysis
namespace NLS.ZakharovShabat

/-- No complex number has a nonzero eigenvector for the actual bounded
Cayley transform of the original whole-line self-adjoint closure. -/
theorem wholeLineCayley_eigenvector_eq_zero (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (ζ : ℂ)
    (f : WholeLineL2) (hf : wholeLineCayley u hu f = ζ • f) : f = 0 :=
  selfAdjointCayley_eigenvector_eq_zero
    (wholeLineMinimalOperator_closure_isSelfAdjoint u hu)
    (wholeLineMinimalOperator_closure_eigenvector_eq_zero u hu) ζ f hf

theorem wholeLineCayley_no_eigenvectors (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) (ζ : ℂ) :
    ¬ ∃ f : WholeLineL2, f ≠ 0 ∧ wholeLineCayley u hu f = ζ • f := by
  rintro ⟨f,hf0,hf⟩
  exact hf0 (wholeLineCayley_eigenvector_eq_zero u hu ζ f hf)

/-- The unchanged original real Hilbert source has the same absence of
Cayley eigenvectors, including at the exceptional point one. -/
theorem source_wholeLineCayley_no_eigenvectors (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) (ζ : ℂ) :
    ¬ ∃ f : WholeLineL2, f ≠ 0 ∧
      wholeLineCayley (sourcePhysicalL2 φ) ((sourcePhysicalL2_realType_iff φ).mpr hφ) f = ζ • f :=
  wholeLineCayley_no_eigenvectors _ _ ζ

end NLS.ZakharovShabat
