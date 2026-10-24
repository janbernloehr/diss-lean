import NLS.ZakharovShabat.SourceSymmetricSignedGaps
import NLS.ZakharovShabat.SourceFloquetEndpointLimit

/-! # Exact boundary levels and gap separation on the symmetric slice

Both ordinary boundary roots have the same signed discriminant level in
each periodic gap. Roots with different gap indices cannot coincide.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both symmetric boundary roots have the indexed periodic endpoint level. -/
theorem sourceDiscriminant_at_symmetricBoundaryRoot_eq_two_gapSign
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (href : realSourceSpatialReflection φ = φ) (b : BoundaryCondition) (n : ℤ) :
    canonicalDiscriminant hp (periodOnePotential φ.val)
      (canonicalPeriodOneBoundaryRoots hp hp1 b φ.val n) = 2 * sourceAbelianGapSign n := by
  apply sourceDiscriminant_eq_two_gapSign_at_endpoint hp hp1 φ.val φ.property n
  have he := sourceBoundaryRoots_opposite_endpoints_of_reflection_fixed hp hp1 φ href n
  cases b <;> rcases he with he | he <;> simp [he.1, he.2]

/-- Equality of any two real boundary roots forces equality of their periodic-gap indices. -/
theorem boundary_root_indices_eq_of_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (b c : BoundaryCondition) (i j : ℤ)
    (he : canonicalPeriodOneBoundaryRoots hp hp1 b φ i =
      canonicalPeriodOneBoundaryRoots hp hp1 c φ j) : i = j := by
  by_contra hij
  have hd := canonicalPeriodicGaps_disjoint hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) hij
  have hi := canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 b φ hφ i
  have hj := canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 c φ hφ j
  rw [he] at hi
  exact Set.disjoint_left.mp hd hi hj

/-- A noncoincident indexed pair excludes every Neumann root at that Dirichlet root. -/
theorem neumannRoots_ne_dirichletRoot_of_indexed_ne
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (m : ℤ)
    (hne : canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ m ≠
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m) (n : ℤ) :
    canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ n ≠
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m := by
  intro he
  have hnm := boundary_root_indices_eq_of_eq hp hp1 φ hφ .neumann .dirichlet n m he
  exact hne (hnm ▸ he)

/-- The Neumann characteristic is nonzero at a noncoincident indexed Dirichlet root. -/
theorem neumannCharacteristic_at_dirichletRoot_ne_zero_of_indexed_ne
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (m : ℤ)
    (hne : canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ m ≠
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m) :
    periodOneBoundaryCharacteristic hp hp1 .neumann φ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ m) ≠ 0 := by
  intro hz
  exact hne (sourceBoundaryRoot_eq_of_zero_mem_gap hp hp1 .neumann ⟨φ,hφ⟩ m _ hz
    (canonicalPeriodOneBoundaryRoots_mem_gap hp hp1 .dirichlet φ hφ m))

/-- Multiplying a coefficient direction by the indexed endpoint levels preserves lp. -/
def sourceGapLevelWeightedDirection (τ : Coeff p) : Coeff p :=
  ⟨fun n => (2 : ℂ) * sourceAbelianGapSign n * τ n, by
    apply ((lp.memℓp τ).norm.const_mul (2 : ℝ)).mono
    intro n
    simp only [norm_mul, norm_ofNat, norm_sourceAbelianGapSign, mul_one]
    rfl⟩

omit [Fact (1 ≤ p)] in
@[simp] theorem sourceGapLevelWeightedDirection_apply (τ : Coeff p) (n : ℤ) :
    sourceGapLevelWeightedDirection τ n = 2 * sourceAbelianGapSign n * τ n := rfl

omit [Fact (1 ≤ p)] in
/-- The indexed endpoint-level multiplier never loses a coordinate. -/
theorem sourceGapLevelWeightedDirection_injective :
    Function.Injective (sourceGapLevelWeightedDirection (p := p)) := by
  intro τ σ he
  ext n
  have hn := congrArg (fun u : Coeff p => u n) he
  have hsign : sourceAbelianGapSign n ≠ 0 := by
    intro h
    have hs := sourceAbelianGapSign_sq n
    simp [h] at hs
  exact mul_left_cancel₀ (mul_ne_zero (by norm_num) hsign) hn

omit [Fact (1 ≤ p)] in
/-- The endpoint-level multiplier preserves real directions. -/
theorem sourceGapLevelWeightedDirection_im_eq_zero (τ : Coeff p)
    (hτ : ∀ n : ℤ, (τ n).im = 0) (n : ℤ) :
    (sourceGapLevelWeightedDirection τ n).im = 0 := by
  simp only [sourceGapLevelWeightedDirection_apply, sourceAbelianGapSign]
  split <;> simp [hτ n]

end NLS.ZakharovShabat
