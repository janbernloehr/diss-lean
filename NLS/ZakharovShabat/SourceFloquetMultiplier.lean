import NLS.ZakharovShabat.SourceCanonicalRootSourceFDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # The canonical Floquet multiplier and its logarithmic derivative

The plus sign uses the canonical root's upper free normalization. The
multiplier is nonzero off the gap cuts. Wherever its value lies in the
principal logarithm's slit plane, that logarithm is an actual primitive
of the discriminant derivative divided by the canonical root.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The multiplier selected by the canonical spectral square root. -/
def sourceFloquetMultiplier (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (z : ℂ) : ℂ :=
  (canonicalDiscriminant hp (periodOnePotential φ) z + sourceCanonicalRoot hp hp1 φ z)/2

/-- The other root of the monodromy characteristic polynomial is its reciprocal. -/
theorem sourceFloquetMultiplier_mul_companion (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ) :
    sourceFloquetMultiplier hp hp1 φ z *
      ((canonicalDiscriminant hp (periodOnePotential φ) z - sourceCanonicalRoot hp hp1 φ z)/2) = 1 := by
  have hs := sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four hp hp1 φ z hz
  unfold sourceFloquetMultiplier
  linear_combination -(1/4 : ℂ) * hs

theorem sourceFloquetMultiplier_ne_zero (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ) :
    sourceFloquetMultiplier hp hp1 φ z ≠ 0 := by
  intro h
  have he := sourceFloquetMultiplier_mul_companion hp hp1 φ z hz
  rw [h, zero_mul] at he
  exact zero_ne_one he

theorem sourceFloquetMultiplier_analyticOnNhd (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) :
    AnalyticOnNhd ℂ (sourceFloquetMultiplier hp hp1 φ) (sourceCanonicalRootDomain hp hp1 φ) := by
  intro z hz
  exact ((analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem φ) z (mem_univ z)).add
    (sourceCanonicalRoot_analyticOnNhd hp hp1 φ z hz)).div_const (c := (2 : ℂ))

/-- Differentiation of the actual multiplier, with its exact root orientation. -/
theorem hasDerivAt_sourceFloquetMultiplier (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ) :
    HasDerivAt (sourceFloquetMultiplier hp hp1 φ)
      (sourceFloquetMultiplier hp hp1 φ z *
        (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z)) z := by
  have hd := (analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem φ) z (mem_univ z)).differentiableAt.hasDerivAt
  have hr := (sourceCanonicalRoot_analyticOnNhd hp hp1 φ z hz).differentiableAt.hasDerivAt
  have h := (hd.add hr).div_const 2
  rw [deriv_sourceCanonicalRoot_eq_discriminant_div_root_mul_deriv hp hp1 φ hφ z hz] at h
  convert! h using 1
  unfold sourceFloquetMultiplier
  field_simp [sourceCanonicalRoot_ne_zero_off_gaps hp hp1 φ z hz]
  ring

/-- The local logarithm is a primitive of the actual critical-root quotient;
its slit-plane hypothesis is explicit and is not claimed globally. -/
theorem hasDerivAt_log_sourceFloquetMultiplier (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (z : ℂ) (hz : z ∈ sourceCanonicalRootDomain hp hp1 φ)
    (hlog : sourceFloquetMultiplier hp hp1 φ z ∈ slitPlane) :
    HasDerivAt (fun w => log (sourceFloquetMultiplier hp hp1 φ w))
      (deriv (canonicalDiscriminant hp (periodOnePotential φ)) z / sourceCanonicalRoot hp hp1 φ z) z := by
  convert (hasDerivAt_sourceFloquetMultiplier hp hp1 φ hφ z hz).clog hlog using 1
  field_simp [sourceFloquetMultiplier_ne_zero hp hp1 φ z hz]

end NLS.ZakharovShabat
