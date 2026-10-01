import NLS.ZakharovShabat.SourceBoundaryRootFloquetPoisson

/-! # Actual Floquet multiplier and local logarithm involution

The fixed-parameter signed discriminant/anti-discriminant combinations
commute globally. At distinct real boundary roots the mixed separation
brackets remove both moving-terminal contributions. The actual moving
Floquet multipliers and their analytic local logarithms therefore commute
within either ordinary boundary family, including collapsed gaps.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The signed fixed-parameter expression whose value at the actual
boundary root is the boundary Floquet multiplier. Away from those roots,
no monodromy eigenvalue claim is made. -/
def sourceBoundaryFloquetExpression (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (z : ℂ) (φ : CoeffPair p) : ℂ :=
  (canonicalDiscriminant hp (periodOnePotential φ) z+
    extensionSign b*sourceAntiDiscriminantCandidate hp hp1 φ z)/2

theorem analyticOnNhd_sourceBoundaryFloquetExpression_joint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => sourceBoundaryFloquetExpression hp hp1 b t.1 t.2) univ := by
  intro t _
  exact ((analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 t (mem_univ _)).add
    (analyticAt_const.mul (analyticOnNhd_sourceAntiDiscriminantCandidate_joint hp hp1 t (mem_univ _)))).div_const

/-- The actual source cotangent of the fixed-parameter combination. -/
theorem fderiv_sourceBoundaryFloquetExpression
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (z : ℂ) (φ : CoeffPair p) :
    fderiv ℂ (sourceBoundaryFloquetExpression hp hp1 b z) φ =
      (2 : ℂ)⁻¹ • (sourceDiscriminantCotangent hp z φ+
        extensionSign b • sourceAntiDiscriminantCotangent hp hp1 z φ) := by
  have hD := (analyticOnNhd_sourceDiscriminant_section hp hp1 z φ (mem_univ _)).differentiableAt
  have hA := (analyticOnNhd_sourceAntiDiscriminant_section hp hp1 z φ (mem_univ _)).differentiableAt
  have hsum : DifferentiableAt ℂ (fun ψ : CoeffPair p =>
      canonicalDiscriminant hp (periodOnePotential ψ) z+
        extensionSign b*sourceAntiDiscriminantCandidate hp hp1 ψ z) φ :=
    hD.fun_add (hA.const_mul (extensionSign b))
  have hr : sourceBoundaryFloquetExpression hp hp1 b z =
      (fun ψ : CoeffPair p => (2 : ℂ)⁻¹*(canonicalDiscriminant hp (periodOnePotential ψ) z+
        extensionSign b*sourceAntiDiscriminantCandidate hp hp1 ψ z)) := by
    funext ψ
    simp only [sourceBoundaryFloquetExpression,div_eq_mul_inv]
    ring
  rw [hr,fderiv_const_mul hsum (2 : ℂ)⁻¹,
    fderiv_fun_add hD (hA.const_mul (extensionSign b)),fderiv_const_mul hA (extensionSign b)]
  rfl

/-- The actual anti-discriminant/discriminant bracket is symmetric in
its two spectral parameters, including coincidence. -/
theorem sourceBracket_anti_discriminant_spectral_symmetric
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair p) (z w : ℂ) :
    sourceBracket h2p (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ z)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ =
    sourceBracket h2p (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ w)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) z) φ := by
  by_cases hzw : z = w
  · subst w
    rfl
  apply mul_left_cancel₀ (sub_ne_zero.mpr hzw)
  have hz := sourceBracket_anti_discriminant hp hp1 h2p φ z w
  have hw := sourceBracket_anti_discriminant hp hp1 h2p φ w z
  linear_combination hz+hw

/-- Every signed fixed-parameter family commutes at every complex source
for finite exponents at least two, without a boundary-root condition. -/
theorem sourceBracket_boundaryFloquetExpressions_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p) (z w : ℂ) :
    sourceBracket h2p (sourceBoundaryFloquetExpression hp hp1 b z)
      (sourceBoundaryFloquetExpression hp hp1 b w) φ = 0 := by
  have hDD := sourceBracket_discriminants_eq_zero hp hp1 h2p φ z w
  have hAA := sourceBracket_anti_anti_eq_zero hp hp1 h2p φ z w
  have hAD := sourceBracket_anti_discriminant_spectral_symmetric hp hp1 h2p φ z w
  change sourceBivector h2p (sourceDiscriminantCotangent hp z φ) (sourceDiscriminantCotangent hp w φ) = 0 at hDD
  change sourceBivector h2p (sourceAntiDiscriminantCotangent hp hp1 z φ)
    (sourceAntiDiscriminantCotangent hp hp1 w φ) = 0 at hAA
  change sourceBivector h2p (sourceAntiDiscriminantCotangent hp hp1 z φ) (sourceDiscriminantCotangent hp w φ) =
    sourceBivector h2p (sourceAntiDiscriminantCotangent hp hp1 w φ) (sourceDiscriminantCotangent hp z φ) at hAD
  have hDA := sourceBivector_antisymm h2p (sourceDiscriminantCotangent hp z φ)
    (sourceAntiDiscriminantCotangent hp hp1 w φ)
  unfold sourceBracket
  rw [fderiv_sourceBoundaryFloquetExpression hp hp1 b z φ,fderiv_sourceBoundaryFloquetExpression hp hp1 b w φ]
  simp only [map_smul,smul_apply,smul_eq_mul,map_add,add_apply]
  rw [hDD,hAA,hDA,hAD]
  ring

/-- The full actual moving multiplier cotangent has the fixed spectral
cotangent and the spectral derivative times the actual root cotangent. -/
theorem fderiv_sourceBoundaryFloquetMultiplier_eq_fixed_and_root
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    fderiv ℂ (sourceBoundaryFloquetMultiplier hp hp1 b n) φ =
      fderiv ℂ (sourceBoundaryFloquetExpression hp hp1 b μ) φ+
        deriv (fun z : ℂ => sourceBoundaryFloquetExpression hp hp1 b z φ) μ •
          fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ := by
  exact NLS.ComplexAnalysis.fderiv_moving_spectral_parameter
    (fun t : ℂ × CoeffPair p => sourceBoundaryFloquetExpression hp hp1 b t.1 t.2)
    (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ
    (analyticOnNhd_sourceBoundaryFloquetExpression_joint hp hp1 b _ (mem_univ _)).differentiableAt
    (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 b φ hreal n).differentiableAt

theorem sourceBracket_boundaryFloquetMultiplier_eq_fixed_and_root
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (G : CoeffPair p → ℂ) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    sourceBracket h2p (sourceBoundaryFloquetMultiplier hp hp1 b n) G φ =
      sourceBracket h2p (sourceBoundaryFloquetExpression hp hp1 b μ) G φ+
        deriv (fun z : ℂ => sourceBoundaryFloquetExpression hp hp1 b z φ) μ*
          sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) G φ := by
  dsimp only
  unfold sourceBracket
  rw [fderiv_sourceBoundaryFloquetMultiplier_eq_fixed_and_root hp hp1 b n φ hreal]
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]

theorem sourceBracket_boundaryRoot_floquetExpression_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p) (n : ℤ) (w : ℂ) :
    sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n)
      (sourceBoundaryFloquetExpression hp hp1 b w) φ =
      (sourceBoundaryRootDiscriminantBracket hp hp1 h2p b φ n w+
        extensionSign b*sourceBoundaryRootAntiDiscriminantBracket hp hp1 h2p b φ n w)/2 := by
  unfold sourceBracket
  rw [fderiv_sourceBoundaryFloquetExpression hp hp1 b w φ]
  simp only [map_smul,smul_eq_mul,map_add]
  change (2 : ℂ)⁻¹*(sourceBoundaryRootDiscriminantBracket hp hp1 h2p b φ n w+
    extensionSign b*sourceBoundaryRootAntiDiscriminantBracket hp hp1 h2p b φ n w) = _
  ring

/-- Root involution makes the mixed bracket with the fixed expression at
another base-source root equal the mixed bracket with its moving multiplier. -/
theorem sourceBracket_boundaryRoot_floquetExpression_at_root
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n m : ℤ) :
    sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n)
      (sourceBoundaryFloquetExpression hp hp1 b (canonicalPeriodOneBoundaryRoots hp hp1 b φ m)) φ =
      sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n)
        (sourceBoundaryFloquetMultiplier hp hp1 b m) φ := by
  rw [sourceBracket_boundaryRoot_floquetExpression_eq,
    sourceBracket_boundaryRoot_floquet_eq_fixed hp hp1 h2p b φ hreal]

/-- All actual moving boundary Floquet multipliers commute within each
family at every real source, including collapsed gaps and equal indices. -/
theorem sourceBracket_boundaryFloquetMultipliers_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n m : ℤ) :
    sourceBracket h2p (sourceBoundaryFloquetMultiplier hp hp1 b n)
      (sourceBoundaryFloquetMultiplier hp hp1 b m) φ = 0 := by
  by_cases hnm : n = m
  · subst m
    exact sourceBracket_self _ _ _
  rw [sourceBracket_boundaryFloquetMultiplier_eq_fixed_and_root hp hp1 h2p b n φ hreal,
    sourceBracket_boundaryRoot_floquet_off_diagonal hp hp1 h2p b φ hreal n m hnm,
    mul_zero,add_zero,sourceBracket_antisymm,
    sourceBracket_boundaryFloquetMultiplier_eq_fixed_and_root hp hp1 h2p b m φ hreal,
    sourceBracket_boundaryFloquetExpressions_eq_zero,
    sourceBracket_boundaryRoot_floquetExpression_at_root hp hp1 h2p b φ hreal,
    sourceBracket_boundaryRoot_floquet_off_diagonal hp hp1 h2p b φ hreal m n (Ne.symm hnm)]
  simp

/-- The actual analytic local Floquet logarithms mutually commute;
both normalization factors are handled by their proved actual cotangents. -/
theorem sourceBracket_boundaryFloquetLogs_eq_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n m : ℤ) :
    sourceBracket h2p (sourceBoundaryFloquetLogAt hp hp1 b n φ)
      (sourceBoundaryFloquetLogAt hp hp1 b m φ) φ = 0 := by
  rw [sourceBracket_boundaryFloquetLogAt_eq_normalized hp hp1 h2p b n φ hreal,
    sourceBracket_right_boundaryFloquetLogAt_eq_normalized hp hp1 h2p b m φ hreal,
    sourceBracket_boundaryFloquetMultipliers_eq_zero hp hp1 h2p b φ hreal]
  simp

end NLS.ZakharovShabat
