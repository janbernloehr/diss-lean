import NLS.ZakharovShabat.BoundaryRootDerivativeInverseBound
import NLS.ZakharovShabat.SourceBoundaryRootDifferential
import NLS.ZakharovShabat.SourceBoundaryDisplacementAnalytic
import NLS.ZakharovShabat.SourcePsiFullProductGapZeros

/-! # Normalized variations of the actual boundary root product

Dividing an arbitrary coefficient direction by the actual root derivatives
preserves its sequence space. The normalized full-product variation takes
exactly the negative original coefficient values at the boundary roots.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

@[simp] theorem displacedRoots_sourceBoundaryDisplacement
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (φ : CoeffPair p) (n : ℤ) :
    displacedRoots (sourceBoundaryDisplacement hp hp1 b φ) n =
      canonicalPeriodOneBoundaryRoots hp hp1 b φ n := by
  simp [displacedRoots]

/-- The actual characteristic is the normalized full displaced-root product. -/
theorem periodOneBoundaryCharacteristic_eq_fullDisplacedProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (φ : CoeffPair p) :
    periodOneBoundaryCharacteristic hp hp1 b φ = fun z => (-1/2 : ℂ) *
      jointSingleSpectralProduct (z, sourceBoundaryDisplacement hp hp1 b φ) := by
  rw [periodOneBoundaryCharacteristic_eq_canonicalProduct]
  have he : displacedRoots (sourceBoundaryDisplacement hp hp1 b φ) =
      canonicalPeriodOneBoundaryRoots hp hp1 b φ :=
    funext (displacedRoots_sourceBoundaryDisplacement hp hp1 b φ)
  change (fun z => (-1/2 : ℂ) * entireSingleSpectralProduct _ z) =
    (fun z => (-1/2 : ℂ) * entireSingleSpectralProduct _ z)
  simp only [he]

theorem deriv_periodOneBoundaryCharacteristic_eq_fullDisplacedProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (φ : CoeffPair p) (z : ℂ) :
    deriv (periodOneBoundaryCharacteristic hp hp1 b φ) z = (-1/2 : ℂ) *
      deriv (fun w => jointSingleSpectralProduct
        (w, sourceBoundaryDisplacement hp hp1 b φ)) z := by
  rw [periodOneBoundaryCharacteristic_eq_fullDisplacedProduct]
  apply deriv_const_mul
  exact (analyticOnNhd_entireSingleSpectralProduct hp _
    (memℓp_displacedRoots (sourceBoundaryDisplacement hp hp1 b φ)) z
    (mem_univ _)).differentiableAt

/-- Inverse actual boundary-root derivatives form a bounded sequence at real type. -/
theorem exists_bound_inv_deriv_periodOneBoundaryCharacteristic_at_roots
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℤ,
      ‖(deriv (periodOneBoundaryCharacteristic hp hp1 b φ)
        (canonicalPeriodOneBoundaryRoots hp hp1 b φ n))⁻¹‖ ≤ B := by
  let a := sourceBoundaryDisplacement hp hp1 b φ
  have hr (n : ℤ) : (displacedRoots a n).im = 0 := by
    simpa only [a, displacedRoots_sourceBoundaryDisplacement] using
      canonicalPeriodOneBoundaryRoots_im_eq_zero hp hp1 b φ hφ n
  have he : displacedBoundaryProduct a = periodOneBoundaryCharacteristic hp hp1 b φ := by
    rw [periodOneBoundaryCharacteristic_eq_canonicalProduct]
    unfold displacedBoundaryProduct
    congr 1
    funext n
    exact displacedRoots_sourceBoundaryDisplacement hp hp1 b φ n
  obtain ⟨B,hB,hbound⟩ := exists_bound_inv_deriv_displacedBoundaryProduct hp hp1 a hr
  exact ⟨B,hB,fun n => by simpa only [he, a, displacedRoots_sourceBoundaryDisplacement] using hbound n⟩

/-- Dividing by the actual root derivatives preserves the original coefficient exponent. -/
def sourceBoundaryNormalizedRootDirection
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (τ : Coeff p) : Coeff p :=
  ⟨fun n => τ n / deriv (periodOneBoundaryCharacteristic hp hp1 b φ)
      (canonicalPeriodOneBoundaryRoots hp hp1 b φ n), by
    obtain ⟨B,_,hB⟩ := exists_bound_inv_deriv_periodOneBoundaryCharacteristic_at_roots hp hp1 b φ hφ
    apply ((lp.memℓp τ).norm.const_mul B).mono
    intro n
    rw [div_eq_mul_inv, norm_mul, mul_comm B]
    exact mul_le_mul_of_nonneg_left (hB n) (norm_nonneg _)⟩

@[simp] theorem sourceBoundaryNormalizedRootDirection_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (τ : Coeff p) (n : ℤ) :
    sourceBoundaryNormalizedRootDirection hp hp1 b φ hφ τ n =
      τ n / deriv (periodOneBoundaryCharacteristic hp hp1 b φ)
        (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) := rfl

/-- The full variation realizes the prescribed negative root values. -/
theorem sourceBoundaryNormalizedRootVariation_at_root
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (τ : Coeff p) (n : ℤ) :
    (-1/2 : ℂ) * sourcePsiFullProductVariation (sourceBoundaryDisplacement hp hp1 b φ)
      (sourceBoundaryNormalizedRootDirection hp hp1 b φ hφ τ)
      (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) = -τ n := by
  rw [← displacedRoots_sourceBoundaryDisplacement hp hp1 b φ n,
    sourcePsiFullProductVariation_at_root hp hp1,
    displacedRoots_sourceBoundaryDisplacement, sourceBoundaryNormalizedRootDirection_apply]
  have hd := deriv_periodOneBoundaryCharacteristic_at_canonicalRoot_ne_zero_of_realType hp hp1 b φ hφ n
  have he := deriv_periodOneBoundaryCharacteristic_eq_fullDisplacedProduct hp hp1 b φ
    (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)
  rw [he] at hd ⊢
  have hJ := (mul_ne_zero_iff.mp hd).2
  field_simp [hJ]

/-- Normalization loses no coefficient information at real-type boundary roots. -/
theorem sourceBoundaryNormalizedRootDirection_injective
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    Function.Injective (sourceBoundaryNormalizedRootDirection hp hp1 b φ hφ) := by
  intro τ σ he
  ext n
  have h := congrArg (fun u : Coeff p => u n) he
  exact (div_left_inj' (deriv_periodOneBoundaryCharacteristic_at_canonicalRoot_ne_zero_of_realType
    hp hp1 b φ hφ n)).mp h

/-- Actual boundary-root derivatives are real for real-type sources. -/
theorem deriv_periodOneBoundaryCharacteristic_at_root_im_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    (deriv (periodOneBoundaryCharacteristic hp hp1 b φ)
      (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)).im = 0 := by
  let a := sourceBoundaryDisplacement hp hp1 b φ
  have hr (j : ℤ) : (displacedRoots a j).im = 0 := by
    simpa only [a, displacedRoots_sourceBoundaryDisplacement] using
      canonicalPeriodOneBoundaryRoots_im_eq_zero hp hp1 b φ hφ j
  have hs (j : ℤ) : ((lp.single p n 1 : Coeff p) j).im = 0 := by
    by_cases hj : j = n <;> simp [lp.single_apply, hj]
  have hz : ((displacedRoots a n).re : ℂ) = displacedRoots a n :=
    Complex.ext rfl (by simpa only [ofReal_im] using (hr n).symm)
  have ht := sourcePsiFullProductVariation_im_eq_zero_of_real_data
    hp hp1 a (lp.single p n 1) hr hs (displacedRoots a n).re
  rw [hz, sourcePsiFullProductVariation_at_root hp hp1] at ht
  simp only [lp.single_apply, Pi.single_eq_same, one_mul, neg_im, neg_eq_zero] at ht
  rw [deriv_periodOneBoundaryCharacteristic_eq_fullDisplacedProduct]
  have he : displacedRoots a n = canonicalPeriodOneBoundaryRoots hp hp1 b φ n :=
    displacedRoots_sourceBoundaryDisplacement hp hp1 b φ n
  rw [he] at ht
  dsimp only [a] at ht
  simp [Complex.mul_im, ht]

/-- Normalizing a real direction preserves reality of every coefficient. -/
theorem sourceBoundaryNormalizedRootDirection_im_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (τ : Coeff p) (hτ : ∀ n : ℤ, (τ n).im = 0) (n : ℤ) :
    (sourceBoundaryNormalizedRootDirection hp hp1 b φ hφ τ n).im = 0 := by
  rw [sourceBoundaryNormalizedRootDirection_apply]
  simp [Complex.div_im, hτ n,
    deriv_periodOneBoundaryCharacteristic_at_root_im_eq_zero hp hp1 b φ hφ n]

end NLS.ZakharovShabat
