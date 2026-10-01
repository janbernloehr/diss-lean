import NLS.ZakharovShabat.SourceBoundaryRootDifferential
import NLS.ZakharovShabat.SourceBoundaryDiscriminantPoisson

/-! # Discriminant Poisson motion of the actual boundary roots

The full root cotangent is the negative normalized characteristic
cotangent. The proved characteristic flow therefore determines the
Poisson bracket of each actual moving Dirichlet or Neumann coordinate
with every fixed-parameter discriminant. Analyticity in that parameter
also determines the coincident-parameter value without a quotient.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual moving boundary-root bracket with a source functional equals
the negative normalized fixed-parameter characteristic bracket. -/
theorem sourceBracket_boundaryRoot_eq_characteristic
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (G : CoeffPair p → ℂ) :
    sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) G φ =
      -(deriv (periodOneBoundaryCharacteristic hp hp1 b φ) (canonicalPeriodOneBoundaryRoots hp hp1 b φ n))⁻¹*
        sourceBracket h2p
          (fun ψ : CoeffPair p => periodOneBoundaryCharacteristic hp hp1 b ψ
            (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)) G φ := by
  change sourceBivector h2p
    (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ)
    (fderiv ℂ G φ) =
      -(deriv (periodOneBoundaryCharacteristic hp hp1 b φ) (canonicalPeriodOneBoundaryRoots hp hp1 b φ n))⁻¹*
        sourceBivector h2p
          (sourceBoundaryCharacteristicCotangent hp hp1 b (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) φ)
          (fderiv ℂ G φ)
  rw [fderiv_canonicalPeriodOneBoundaryRoot_eq_cotangent hp hp1 b φ hreal n]
  simp only [map_smul,smul_apply,smul_eq_mul]

/-- Clearing the nonzero characteristic derivative balances the two
actual brackets. The second functional need not be analytic. -/
theorem sourceBracket_boundaryRoot_balance
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (G : CoeffPair p → ℂ) :
    deriv (periodOneBoundaryCharacteristic hp hp1 b φ) (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)*
      sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) G φ =
        -sourceBracket h2p
          (fun ψ : CoeffPair p => periodOneBoundaryCharacteristic hp hp1 b ψ
            (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)) G φ := by
  rw [sourceBracket_boundaryRoot_eq_characteristic hp hp1 h2p b φ hreal n G]
  have hd := deriv_periodOneBoundaryCharacteristic_at_canonicalRoot_ne_zero_of_realType hp hp1 b φ hreal n
  field_simp

/-- The actual root/discriminant bracket, with the root coordinate moving
in the first functional and the spectral parameter fixed in the second. -/
def sourceBoundaryRootDiscriminantBracket
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p) (n : ℤ) (w : ℂ) : ℂ :=
  sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n)
    (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ

/-- At any base source the fixed-source bracket is entire in its second
spectral parameter, as follows from the actual operator-valued differential. -/
theorem analyticOnNhd_sourceBoundaryRootDiscriminantBracket_spectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceBoundaryRootDiscriminantBracket hp hp1 h2p b φ n) univ := by
  let L := sourceBivector h2p
    (fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ)
  intro w _
  have hc := ((analyticOnNhd_sourceDiscriminantCotangent_joint hp hp1) (w,φ) (mem_univ _)).comp
    (f := fun t : ℂ => (t,φ)) (analyticAt_id.prod analyticAt_const)
  exact (L.analyticAt _).comp hc

/-- The actual moving boundary coordinate has the prescribed signed
discriminant bracket at all parameters, with both denominators cleared. -/
theorem sourceBoundaryRootDiscriminantBracket_mul
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (w : ℂ) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    2*(μ-w)*(deriv (periodOneBoundaryCharacteristic hp hp1 b φ) μ*
      sourceBoundaryRootDiscriminantBracket hp hp1 h2p b φ n w) =
        extensionSign b*sourceAntiDiscriminantCandidate hp hp1 φ μ*
          periodOneBoundaryCharacteristic hp hp1 b φ w := by
  dsimp only
  rw [sourceBoundaryRootDiscriminantBracket,
    sourceBracket_boundaryRoot_balance hp hp1 h2p b φ hreal n]
  have hf := sourceBracket_boundary_discriminant_at_canonicalRoot hp hp1 h2p b φ n w
  dsimp only at hf
  linear_combination -hf

/-- At distinct spectral parameters this is the literal root-motion
quotient, with its original boundary sign and characteristic normalization. -/
theorem sourceBoundaryRootDiscriminantBracket_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (w : ℂ)
    (hw : canonicalPeriodOneBoundaryRoots hp hp1 b φ n ≠ w) :
    sourceBoundaryRootDiscriminantBracket hp hp1 h2p b φ n w =
      (extensionSign b*sourceAntiDiscriminantCandidate hp hp1 φ (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)*
        periodOneBoundaryCharacteristic hp hp1 b φ w)/
          (2*(canonicalPeriodOneBoundaryRoots hp hp1 b φ n-w)*
            deriv (periodOneBoundaryCharacteristic hp hp1 b φ) (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)) := by
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hw))
    (deriv_periodOneBoundaryCharacteristic_at_canonicalRoot_ne_zero_of_realType hp hp1 b φ hreal n))).mpr
  have hf := sourceBoundaryRootDiscriminantBracket_mul hp hp1 h2p b φ hreal n w
  dsimp only at hf
  linear_combination hf

/-- The entire bracket resolves the apparent coincident-parameter
singularity to minus one half the signed actual anti-discriminant. -/
theorem sourceBoundaryRootDiscriminantBracket_at_root
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    sourceBoundaryRootDiscriminantBracket hp hp1 h2p b φ n (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) =
      -extensionSign b*sourceAntiDiscriminantCandidate hp hp1 φ (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)/2 := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
  let d := deriv (periodOneBoundaryCharacteristic hp hp1 b φ) μ
  let B := sourceBoundaryRootDiscriminantBracket hp hp1 h2p b φ n
  have hB : DifferentiableAt ℂ B μ :=
    (analyticOnNhd_sourceBoundaryRootDiscriminantBracket_spectral hp hp1 h2p b φ n μ (mem_univ _)).differentiableAt
  have hχ := (analyticOnNhd_periodOneBoundaryCharacteristic hp hp1 b φ μ (mem_univ _)).differentiableAt.hasDerivAt
  have heq : (fun w : ℂ => 2*(μ-w)*(d*B w)) =
      (fun w => extensionSign b*sourceAntiDiscriminantCandidate hp hp1 φ μ*
        periodOneBoundaryCharacteristic hp hp1 b φ w) := by
    funext w
    exact sourceBoundaryRootDiscriminantBracket_mul hp hp1 h2p b φ hreal n w
  have hleft := (((hasDerivAt_const μ μ).sub (hasDerivAt_id μ)).const_mul (2 : ℂ)).mul
    (hB.hasDerivAt.const_mul d)
  have hright := hχ.const_mul (extensionSign b*sourceAntiDiscriminantCandidate hp hp1 φ μ)
  change HasDerivAt (fun w : ℂ => 2*(μ-w)*(d*B w))
    (2*(0-1)*(d*B μ)+2*(μ-μ)*(d*deriv B μ)) μ at hleft
  rw [heq] at hleft
  have hd := hleft.unique hright
  simp only [sub_self,mul_zero,zero_mul,add_zero,zero_sub] at hd
  have hdn : d ≠ 0 :=
    deriv_periodOneBoundaryCharacteristic_at_canonicalRoot_ne_zero_of_realType hp hp1 b φ hreal n
  change 2*(-1)*(d*B μ) = extensionSign b*sourceAntiDiscriminantCandidate hp hp1 φ μ*d at hd
  change B μ = -extensionSign b*sourceAntiDiscriminantCandidate hp hp1 φ μ/2
  apply (mul_left_cancel₀ hdn)
  linear_combination (1/2 : ℂ)*(-hd)

/-- A collapsed indexed periodic gap makes either actual boundary root
stationary under every discriminant Hamiltonian, including at coincidence. -/
theorem sourceBoundaryRootDiscriminantBracket_eq_zero_of_collapsed_gap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0) (w : ℂ) :
    sourceBoundaryRootDiscriminantBracket hp hp1 h2p b φ n w = 0 := by
  have hδ := sourceAntiDiscriminant_at_canonicalBoundaryRoot_eq_zero_of_collapsed_gap hp hp1 b φ hreal n hgap
  by_cases hw : canonicalPeriodOneBoundaryRoots hp hp1 b φ n = w
  · rw [← hw,sourceBoundaryRootDiscriminantBracket_at_root hp hp1 h2p b φ hreal n,hδ]
    simp
  · rw [sourceBoundaryRootDiscriminantBracket_eq hp hp1 h2p b φ hreal n w hw,hδ]
    simp

end NLS.ZakharovShabat
