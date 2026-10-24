import NLS.ZakharovShabat.SourceBoundaryNormalizedRootVariation
import NLS.ZakharovShabat.SymmetricBoundaryRootLevels
import NLS.ZakharovShabat.SymmetricSignedGapCollapsedKernel
import NLS.ZakharovShabat.SourcePsiFullProductResolventExterior

/-! # Entire product variation attached to the actual gradient matrix

Normalize the endpoint-level-weighted direction by the Neumann root
derivatives. The matrix coordinate equations are then exactly the
Dirichlet values of this entire variation.
-/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

def symmetricSignedGapKernelRootDirection (φ : realTypeSourceSubmodule 2) (τ : Coeff 2) : Coeff 2 :=
  sourceBoundaryNormalizedRootDirection (by simp) (by norm_num) .neumann φ.val φ.property
    (sourceGapLevelWeightedDirection τ)

def symmetricSignedGapKernelVariation (φ : realTypeSourceSubmodule 2) (τ : Coeff 2) (z : ℂ) : ℂ :=
  (-1/2 : ℂ) * sourcePsiFullProductVariation
    (sourceBoundaryDisplacement (by simp) (by norm_num) .neumann φ.val)
    (symmetricSignedGapKernelRootDirection φ τ) z

theorem symmetricSignedGapKernelVariation_at_neumannRoot
    (φ : realTypeSourceSubmodule 2) (τ : Coeff 2) (n : ℤ) :
    symmetricSignedGapKernelVariation φ τ
      (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .neumann φ.val n) =
      -(2 * sourceAbelianGapSign n * τ n) :=
  sourceBoundaryNormalizedRootVariation_at_root (by simp) (by norm_num) .neumann
    φ.val φ.property (sourceGapLevelWeightedDirection τ) n

/-- At a noncoincident Dirichlet root, the entire variation is exactly the matrix defect. -/
theorem symmetricSignedGapKernelVariation_at_dirichletRoot_of_ne
    (φ : realTypeSourceSubmodule 2) (href : realSourceSpatialReflection φ = φ)
    (τ : Coeff 2) (m : ℤ)
    (hne : canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .neumann φ.val m ≠
      canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ.val m) :
    symmetricSignedGapKernelVariation φ τ
      (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ.val m) =
      (2 * sourceAbelianGapSign m) * (τ m -
        symmetricSignedGapGradientMatrix φ.val φ.property (congrArg Subtype.val href) τ m) := by
  classical
  let μ := canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ.val m
  let ν := canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .neumann φ.val
  let χ := periodOneBoundaryCharacteristic (by simp) (by norm_num) .neumann φ.val
  let Δ := canonicalDiscriminant (by simp) (periodOnePotential φ.val)
  let M := symmetricSignedGapDerivativeMatrix φ.val φ.property (congrArg Subtype.val href)
  let A := symmetricSignedGapGradientMatrix φ.val φ.property (congrArg Subtype.val href)
  let a := sourceBoundaryDisplacement (by simp) (by norm_num) .neumann φ.val
  let η := symmetricSignedGapKernelRootDirection φ τ
  let v : Coeff 2 := lp.single 2 m 1 - M (lp.single 2 m 1)
  let q : ℤ → ℂ := fun n => τ n * v n
  have hq : Summable q := (Coeff.summable_norm_dualPairing τ v).of_norm
  have hqsum : (∑' n : ℤ, q n) = τ m - A τ m := by
    change Coeff.dualPairing τ (lp.single 2 m 1 - M (lp.single 2 m 1)) = _
    rw [map_sub, Coeff.dualPairing_hilbert_single_right]
    congr 1
    exact (symmetricSignedGapGradientMatrix_apply φ.val φ.property
      (congrArg Subtype.val href) τ m).symm
  have hχ : χ μ ≠ 0 := neumannCharacteristic_at_dirichletRoot_ne_zero_of_indexed_ne
    (by simp) (by norm_num) φ.val φ.property m hne
  have hΔ : Δ μ = 2 * sourceAbelianGapSign m :=
    sourceDiscriminant_at_symmetricBoundaryRoot_eq_two_gapSign
      (by simp) (by norm_num) φ href .dirichlet m
  have hΔne : Δ μ ≠ 0 := by
    rw [hΔ]
    have hs := sourceAbelianGapSign_sq m
    intro he
    have hz : sourceAbelianGapSign m = 0 := (mul_eq_zero.mp he).resolve_left (by norm_num)
    simp [hz] at hs
  have hneq (n : ℤ) : ν n ≠ μ := neumannRoots_ne_dirichletRoot_of_indexed_ne
    (by simp) (by norm_num) φ.val φ.property m hne n
  have hη (n : ℤ) : η n = τ n * Δ (ν n) / deriv χ (ν n) := by
    have hl := sourceDiscriminant_at_symmetricBoundaryRoot_eq_two_gapSign
      (by simp) (by norm_num) φ href .neumann n
    change _ = τ n * canonicalDiscriminant (by simp) (periodOnePotential φ.val) _ / _
    rw [hl]
    change (2 * sourceAbelianGapSign n * τ n) / _ = _
    ring
  have hres (n : ℤ) : η n / (ν n - μ) = (Δ μ / χ μ) * q n := by
    have hd := deriv_periodOneBoundaryCharacteristic_at_canonicalRoot_ne_zero_of_realType
      (by simp) (by norm_num) .neumann φ.val φ.property n
    change deriv χ (ν n) ≠ 0 at hd
    have hm := symmetricSignedGapDerivativeMatrix_single_of_ne
      φ.val φ.property (congrArg Subtype.val href) n m (hneq n)
    have hs : (lp.single 2 m 1 : Coeff 2) n = if n = m then 1 else 0 := by
      by_cases h : n = m <;> simp [lp.single_apply, h]
    change M (lp.single 2 m 1) n = (if n = m then 1 else 0) -
      Δ (ν n) * χ μ / (Δ μ * (ν n - μ) * deriv χ (ν n)) at hm
    rw [hη]
    change _ = (Δ μ / χ μ) * (τ n * ((lp.single 2 m 1 : Coeff 2) n - M (lp.single 2 m 1) n))
    rw [hs, hm]
    field_simp [hχ, hΔne, sub_ne_zero.mpr (hneq n), hd]
    ring
  have hsum : Summable (fun n : ℤ => η n / (displacedRoots a n - μ)) := by
    have he (n : ℤ) : η n / (displacedRoots a n - μ) = (Δ μ / χ μ) * q n := by
      simpa only [a, displacedRoots_sourceBoundaryDisplacement] using hres n
    simpa only [he] using hq.mul_left (Δ μ / χ μ)
  have havoid (n : ℤ) : μ ≠ displacedRoots a n := by
    simpa only [a, displacedRoots_sourceBoundaryDisplacement] using (hneq n).symm
  have hp := sourcePsiFullProductVariation_eq_product_mul_resolvent
    (by simp) (by norm_num) a η μ havoid hsum
  have hprod : χ μ = (-1/2 : ℂ) * jointSingleSpectralProduct (μ,a) :=
    congrFun (periodOneBoundaryCharacteristic_eq_fullDisplacedProduct
      (by simp) (by norm_num) .neumann φ.val) μ
  change (-1/2 : ℂ) * sourcePsiFullProductVariation a η μ = _
  rw [hp]
  have hsumid : (∑' n : ℤ, η n / (displacedRoots a n - μ)) =
      (Δ μ / χ μ) * (τ m - A τ m) := by
    simp_rw [show ∀ n : ℤ, displacedRoots a n = ν n from
      fun n => displacedRoots_sourceBoundaryDisplacement (by simp) (by norm_num) .neumann φ.val n,
      hres]
    rw [tsum_mul_left, hqsum]
  rw [hsumid]
  rw [← mul_assoc, ← hprod, ← hΔ]
  field_simp [hχ]
  rfl

/-- The same exact identity holds at collapsed pairs, using the filled diagonal value two. -/
theorem symmetricSignedGapKernelVariation_at_dirichletRoot
    (φ : realTypeSourceSubmodule 2) (href : realSourceSpatialReflection φ = φ)
    (τ : Coeff 2) (m : ℤ) :
    symmetricSignedGapKernelVariation φ τ
      (canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ.val m) =
      (2 * sourceAbelianGapSign m) * (τ m -
        symmetricSignedGapGradientMatrix φ.val φ.property (congrArg Subtype.val href) τ m) := by
  by_cases he : canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .neumann φ.val m =
      canonicalPeriodOneBoundaryRoots (by simp) (by norm_num) .dirichlet φ.val m
  · rw [← he, symmetricSignedGapKernelVariation_at_neumannRoot,
      symmetricSignedGapGradientMatrix_apply_of_coincident φ.val φ.property
        (congrArg Subtype.val href) τ m he]
    ring
  · exact symmetricSignedGapKernelVariation_at_dirichletRoot_of_ne φ href τ m he

end NLS.ZakharovShabat
