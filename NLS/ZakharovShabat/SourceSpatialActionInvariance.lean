import NLS.ZakharovShabat.SourceIsospectralSet
import NLS.ZakharovShabat.SourceSobolevMomentumTranslation
import NLS.ZakharovShabat.SourceBirkhoffJacobian
import NLS.ZakharovShabat.SourceSobolevFiniteGapDensity

/-! # Actual spatial invariance of source actions

The original spectral actions are constant under the physical translation
of every real source. On H¹ this gives the actual momentum bracket. A
closed rectangular coordinate stays zero along the entire translation
orbit, so its momentum derivative vanishes without a polar division.
-/
noncomputable section
open Set Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Actual indexed actions are invariant under the physical spatial group. -/
theorem sourceComplexAction_spatialTranslation_finite_exponent (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (t : ℝ) (n : ℤ) :
    sourceComplexAction hp hp1 n (sourceSpatialTranslation t φ.val) =
      sourceComplexAction hp hp1 n φ.val := by
  let ψ : realTypeSourceSubmodule p :=
    ⟨sourceSpatialTranslation t φ.val,sourceSpatialTranslation_realType t φ.val φ.property⟩
  rw [sourceComplexAction_eq_sourceRealAction hp hp1 n ψ.val ψ.property,
    sourceComplexAction_eq_sourceRealAction hp hp1 n φ.val φ.property]
  exact sourceRealAction_eq_of_isospectral hp hp1 φ ψ
    ⟨sourcePeriodicSpectrum_spatialTranslation hp t φ.val,
      sourcePeriodicAlgebraicMultiplicity_spatialTranslation hp t φ.val⟩ n

/-- Every actual action has zero physical momentum bracket on real H¹. -/
theorem sourceActionDifferential_spatial_eq_zero
    (a : realTypeSobolevSourceLocus) (n : ℤ) :
    (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
      (sobolevSourceInclusion a.val)) (sourceSobolevSpatialDerivative a.val) = 0 := by
  rw [← sourceBivector_momentum]
  exact sourceBivector_momentum_eq_zero_of_translation_invariant a.val _
    (analyticAt_sourceComplexAction_of_realType (by simp) (by norm_num) n
      (sobolevSourceInclusion a.val) a.property).differentiableAt
    (sourceComplexAction_spatialTranslation_finite_exponent (by simp) (by norm_num)
      ⟨sobolevSourceInclusion a.val,a.property⟩ · n)

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)}
  {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- A selected collapsed gap has zero rectangular translation velocity. -/
theorem map_coordinates_spatial_of_closed_gap
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : realTypeSobolevSourceLocus) (n : ℤ)
    (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion a.val)) (periodOnePotential_mem _) n = 0) :
    (fderiv ℂ (fun ψ => (sourceBirkhoffMap (by simp) (by norm_num) s ψ).1 n)
      (sobolevSourceInclusion a.val)) (sourceSobolevSpatialDerivative a.val) = 0 ∧
    (fderiv ℂ (fun ψ => (sourceBirkhoffMap (by simp) (by norm_num) s ψ).2 n)
      (sobolevSourceInclusion a.val)) (sourceSobolevSpatialDerivative a.val) = 0 := by
  let φ := sobolevSourceInclusion a.val
  have hclosed (t : ℝ) := D.real_closed_gap_zero (sourceSpatialTranslation t φ)
    (D.real_subset (sourceSpatialTranslation_realType t φ a.property))
    (sourceSpatialTranslation_realType t φ a.property) n
    (by simpa only [sourcePeriodicGapDisplacement_apply,sourceCanonicalPeriodicGap_spatialTranslation] using hn)
  let ex := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp
    (ContinuousLinearMap.fst ℂ (Coeff 2) (Coeff 2))
  let ey := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).comp
    (ContinuousLinearMap.snd ℂ (Coeff 2) (Coeff 2))
  have hx := hasDerivAt_sourceSpatialTranslation_functional a.val
    (fun ψ => (sourceBirkhoffMap (by simp) (by norm_num) s ψ).1 n)
    (ex.differentiableAt.comp φ (D.analytic φ (D.real_subset a.property)).differentiableAt)
  have hy := hasDerivAt_sourceSpatialTranslation_functional a.val
    (fun ψ => (sourceBirkhoffMap (by simp) (by norm_num) s ψ).2 n)
    (ey.differentiableAt.comp φ (D.analytic φ (D.real_subset a.property)).differentiableAt)
  have hex : (fun r : ℝ => (sourceBirkhoffMap (by simp) (by norm_num) s
      (sourceSpatialTranslation r φ)).1 n) = (fun _ => 0) := funext (fun r => (hclosed r).1)
  have hey : (fun r : ℝ => (sourceBirkhoffMap (by simp) (by norm_num) s
      (sourceSpatialTranslation r φ)).2 n) = (fun _ => 0) := funext (fun r => (hclosed r).2)
  rw [hex] at hx
  rw [hey] at hy
  rw [sourceBivector_momentum] at hx hy
  exact ⟨hx.unique (hasDerivAt_const 0 (0 : ℂ)),hy.unique (hasDerivAt_const 0 (0 : ℂ))⟩

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
