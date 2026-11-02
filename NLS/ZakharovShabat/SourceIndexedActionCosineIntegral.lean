import NLS.ZakharovShabat.SourceIndexedActionAnalytic
import NLS.ZakharovShabat.SourcePrimitivePowerAction
import NLS.ZakharovShabat.SourcePrimitivePowerRealIntegral

/-! # The actual indexed action as a real gap integral

The first primitive moment is already proved equal to the original
contour action. Its real-source cosine formula therefore applies to the
circle-independent indexed action, including collapsed gaps and index zero.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceIndexedAction_eq_cosineIntegral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    sourceIndexedAction hp hp1 n φ =
      (((canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re / Real.pi *
        ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ * sourceRealGapCosineProfile hp hp1 φ n θ : ℝ) : ℂ) := by
  obtain ⟨W,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas hp hp1
  have h1 := A.moment_one n (A.realType_subset_domain hφ)
  rw [sourceComplexAction_eq_sourceRealAction hp hp1 n φ hφ] at h1
  rw [sourceIndexedAction_eq_sourceRealAction hp hp1 n φ hφ,← h1]
  simpa only [mul_zero,zero_add,pow_one] using A.real_odd_moment_eq_cosineIntegral ⟨φ,hφ⟩ n 0

end NLS.ZakharovShabat
