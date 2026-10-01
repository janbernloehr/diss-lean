import NLS.ZakharovShabat.CanonicalPeriodOneBoundaryAnalytic
import NLS.ZakharovShabat.SourceBoundaryPoissonGradient
import NLS.ComplexAnalysis.BanachC1ImplicitDerivative
import NLS.ComplexAnalysis.MixedSpectralSourceDerivative

/-! # Actual differentials of the canonical ordinary boundary roots

Every canonical root satisfies the original characteristic equation.
At real-type sources the original multiplicity is one and the actual
coordinate is analytic. Differentiating the zero equation determines its
full source cotangent, including central indices and collapsed gaps.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every actual canonical boundary coordinate is a zero of its original
characteristic at every complex source. -/
theorem periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (φ : CoeffPair p) (n : ℤ) :
    periodOneBoundaryCharacteristic hp hp1 b φ (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) = 0 :=
  (periodOneBoundaryCharacteristic_eq_zero_iff hp hp1 b φ _).mpr
    ((canonicalPeriodOneBoundaryRoots_exhaustive hp hp1 b φ _).mpr ⟨n,rfl⟩)

/-- The anti-discriminant square identity holds at every actual canonical
Dirichlet or Neumann root, whether or not the complex root is simple. -/
theorem sourceDiscriminant_sq_sub_four_at_canonicalBoundaryRoot
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (φ : CoeffPair p) (n : ℤ) :
    (canonicalDiscriminant hp (periodOnePotential φ) (canonicalPeriodOneBoundaryRoots hp hp1 b φ n))^2-4 =
      (sourceAntiDiscriminantCandidate hp hp1 φ (canonicalPeriodOneBoundaryRoots hp hp1 b φ n))^2 := by
  have hz := periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero hp hp1 b φ n
  have hs := sourceDiscriminant_sq_sub_four hp hp1 φ (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)
  cases b <;> simpa [hz] using hs

/-- At a collapsed real periodic gap the actual anti-discriminant
vanishes at either ordinary boundary root. -/
theorem sourceAntiDiscriminant_at_canonicalBoundaryRoot_eq_zero_of_collapsed_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0) :
    sourceAntiDiscriminantCandidate hp hp1 φ (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) = 0 := by
  have hend : canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n =
      canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n := by
    exact (sub_eq_zero.mp hgap).symm
  have hroot := canonicalPeriodOneBoundaryRoots_eq_of_collapsed_gap hp hp1 b φ hreal n hend
  apply sq_eq_zero_iff.mp
  rw [← sourceDiscriminant_sq_sub_four_at_canonicalBoundaryRoot hp hp1 b φ n,
    canonicalDiscriminant_sq_sub_four_eq_pair_mul hp hp1 _ (periodOnePotential_mem φ) n,hroot]
  simp

/-- The spectral derivative of the actual boundary characteristic never
vanishes at a real-type canonical root, including collapsed periodic gaps. -/
theorem deriv_periodOneBoundaryCharacteristic_at_canonicalRoot_ne_zero_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    deriv (periodOneBoundaryCharacteristic hp hp1 b φ) (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) ≠ 0 := by
  have ha := analyticOnNhd_periodOneBoundaryCharacteristic hp hp1 b φ
    (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) (mem_univ _)
  have ho : analyticOrderAt (periodOneBoundaryCharacteristic hp hp1 b φ)
      (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) = 1 := by
    rw [analyticOrderAt_periodOneBoundaryCharacteristic,
      canonicalPeriodOneBoundaryRoots_algebraicMultiplicity_eq_one_of_realType hp hp1 b φ hreal n]
    rfl
  have hd : analyticOrderAt (deriv (periodOneBoundaryCharacteristic hp hp1 b φ))
      (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) = 0 :=
    analyticOrderAt_deriv_of_pos ha (n := 0) (by simpa using ho)
  intro hzero
  exact (ha.deriv.analyticOrderAt_ne_zero.mpr hzero) hd

/-- Differentiating the actual canonical root equation balances its moving
coordinate derivative against the fixed-parameter characteristic cotangent. -/
theorem fderiv_canonicalPeriodOneBoundaryRoot_balance
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (h : CoeffPair p) :
    deriv (periodOneBoundaryCharacteristic hp hp1 b φ) (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)*
      ((fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ) h) =
        -sourceBoundaryCharacteristicCotangent hp hp1 b (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) φ h := by
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n
  let F : ℂ × CoeffPair p → ℂ := fun t => periodOneBoundaryCharacteristic hp hp1 b t.2 t.1
  have hF : DifferentiableAt ℂ F (μ φ,φ) :=
    (analyticOnNhd_periodOneBoundaryCharacteristic_joint hp hp1 b (μ φ,φ) (mem_univ _)).differentiableAt
  have hμ : DifferentiableAt ℂ μ φ :=
    (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 b φ hreal n).differentiableAt
  have hzero : ∀ᶠ ψ in 𝓝 φ, F (μ ψ,ψ) = 0 :=
    Filter.Eventually.of_forall (fun ψ => periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero hp hp1 b ψ n)
  have hbalance := NLS.ComplexAnalysis.implicitBanachRoot_fderiv_balance F μ φ hF hμ hzero h
  have hsplit : ((fderiv ℂ μ φ) h,h) =
      ((fderiv ℂ μ φ) h,(0 : CoeffPair p)) + ((0 : ℂ),h) := by
    ext <;> simp
  rw [hsplit,map_add] at hbalance
  have hspectral : (fderiv ℂ F (μ φ,φ)) ((fderiv ℂ μ φ) h,0) =
      ((fderiv ℂ μ φ) h)*deriv (periodOneBoundaryCharacteristic hp hp1 b φ) (μ φ) := by
    rw [NLS.ComplexAnalysis.deriv_spectral_section_eq_fderiv F (μ φ) φ hF]
    have hpvec : ((fderiv ℂ μ φ) h,(0 : CoeffPair p)) =
        ((fderiv ℂ μ φ) h) • ((1 : ℂ),(0 : CoeffPair p)) := by
      ext <;> simp
    rw [hpvec,map_smul,smul_eq_mul]
  have hsource : (fderiv ℂ F (μ φ,φ)) (0,h) =
      sourceBoundaryCharacteristicCotangent hp hp1 b (μ φ) φ h := by
    rw [sourceBoundaryCharacteristicCotangent,
      NLS.ComplexAnalysis.fderiv_source_section_eq_joint F (μ φ) φ hF,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply]
  rw [hspectral,hsource] at hbalance
  rw [mul_comm]
  exact eq_neg_of_add_eq_zero_left hbalance

/-- The actual root source derivative in each direction is the negative
characteristic derivative divided by its nonzero spectral derivative. -/
theorem fderiv_canonicalPeriodOneBoundaryRoot_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (h : CoeffPair p) :
    (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ) h =
      -sourceBoundaryCharacteristicCotangent hp hp1 b (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) φ h /
        deriv (periodOneBoundaryCharacteristic hp hp1 b φ) (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) := by
  apply (eq_div_iff (deriv_periodOneBoundaryCharacteristic_at_canonicalRoot_ne_zero_of_realType
    hp hp1 b φ hreal n)).mpr
  rw [mul_comm]
  exact fderiv_canonicalPeriodOneBoundaryRoot_balance hp hp1 b φ hreal n h

/-- Equality of the full continuous root cotangent with the normalized
actual characteristic cotangent, valid at every real-type source. -/
theorem fderiv_canonicalPeriodOneBoundaryRoot_eq_cotangent
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ =
      -(deriv (periodOneBoundaryCharacteristic hp hp1 b φ) (canonicalPeriodOneBoundaryRoots hp hp1 b φ n))⁻¹ •
        sourceBoundaryCharacteristicCotangent hp hp1 b (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) φ := by
  ext h
  rw [fderiv_canonicalPeriodOneBoundaryRoot_apply hp hp1 b φ hreal n]
  simp only [smul_apply,smul_eq_mul,div_eq_mul_inv]
  ring

end NLS.ZakharovShabat
