import NLS.ZakharovShabat.SourceBoundaryTerminalDifferential
import NLS.ZakharovShabat.SourceBoundaryRootPoisson
import NLS.ZakharovShabat.SourceAntiDiscriminantPoisson

/-! # Actual moving-terminal and Floquet discriminant brackets

The root motion contributes to both terminal differentials. Differentiating
the original unimodular identity cancels the other characteristic in the
moving anti-discriminant flow. The signed Floquet multiplier has a nonzero
value, so its normalized bracket is defined even at collapsed gaps.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Spectral differentiation of the actual unimodular identity, on the
whole complex source space rather than just at boundary roots. -/
theorem sourceDiscriminant_mul_deriv_eq_anti_and_characteristics
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (z : ℂ) :
    canonicalDiscriminant hp (periodOnePotential φ) z*
      deriv (canonicalDiscriminant hp (periodOnePotential φ)) z =
        sourceAntiDiscriminantCandidate hp hp1 φ z*deriv (sourceAntiDiscriminantCandidate hp hp1 φ) z-
          2*(deriv (periodOneBoundaryCharacteristic hp hp1 .dirichlet φ) z*
              periodOneBoundaryCharacteristic hp hp1 .neumann φ z+
            periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z*
              deriv (periodOneBoundaryCharacteristic hp hp1 .neumann φ) z) := by
  have hΔ := (analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem φ)
    z (mem_univ _)).differentiableAt.hasDerivAt
  have hδ := (analyticOnNhd_sourceAntiDiscriminantCandidate hp hp1 φ z (mem_univ _)).differentiableAt.hasDerivAt
  have hD := (analyticOnNhd_periodOneBoundaryCharacteristic hp hp1 .dirichlet φ z (mem_univ _)).differentiableAt.hasDerivAt
  have hN := (analyticOnNhd_periodOneBoundaryCharacteristic hp hp1 .neumann φ z (mem_univ _)).differentiableAt.hasDerivAt
  have heq : (fun w : ℂ => canonicalDiscriminant hp (periodOnePotential φ) w*
      canonicalDiscriminant hp (periodOnePotential φ) w-4) =
    (fun w => sourceAntiDiscriminantCandidate hp hp1 φ w*sourceAntiDiscriminantCandidate hp hp1 φ w-
      4*periodOneBoundaryCharacteristic hp hp1 .dirichlet φ w*periodOneBoundaryCharacteristic hp hp1 .neumann φ w) := by
    funext w
    simpa only [pow_two] using sourceDiscriminant_sq_sub_four hp hp1 φ w
  have hl := (hΔ.mul hΔ).sub (hasDerivAt_const z (4 : ℂ))
  change HasDerivAt (fun w : ℂ => canonicalDiscriminant hp (periodOnePotential φ) w*
    canonicalDiscriminant hp (periodOnePotential φ) w-4) _ z at hl
  have hr := (hδ.mul hδ).sub ((hD.const_mul (4 : ℂ)).mul hN)
  rw [heq] at hl
  have hd := hl.unique hr
  linear_combination (1/2 : ℂ)*hd

/-- The moving terminal discriminant bracket has the fixed-parameter
bracket and the actual root-motion contribution. -/
theorem sourceBracket_boundaryTerminalDiscriminant_eq_fixed_and_root
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (G : CoeffPair p → ℂ) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    sourceBracket h2p (sourceBoundaryTerminalDiscriminant hp hp1 b n) G φ =
      sourceBracket h2p (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) μ) G φ+
        deriv (canonicalDiscriminant hp (periodOnePotential φ)) μ*
          sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) G φ := by
  dsimp only
  unfold sourceBracket
  rw [fderiv_sourceBoundaryTerminalDiscriminant hp hp1 b n φ hreal]
  simp only [sourceDiscriminantCotangent,map_add,map_smul,add_apply,smul_apply,smul_eq_mul]

/-- In particular, moving the anti-discriminant's terminal is different
from keeping the base-source terminal fixed. -/
theorem sourceBracket_boundaryTerminalAntiDiscriminant_eq_fixed_and_root
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (G : CoeffPair p → ℂ) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    sourceBracket h2p (sourceBoundaryTerminalAntiDiscriminant hp hp1 b n) G φ =
      sourceBracket h2p (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ μ) G φ+
        deriv (sourceAntiDiscriminantCandidate hp hp1 φ) μ*
          sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) G φ := by
  dsimp only
  unfold sourceBracket
  rw [fderiv_sourceBoundaryTerminalAntiDiscriminant hp hp1 b n φ hreal]
  simp only [sourceAntiDiscriminantCotangent,map_add,map_smul,add_apply,smul_apply,smul_eq_mul]

/-- The actual moving terminal discriminant has the signed root kernel,
with the spectral derivative of the discriminant as an extra factor. -/
theorem sourceBracket_boundaryTerminalDiscriminant_discriminant_mul
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (w : ℂ) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    2*(μ-w)*deriv (periodOneBoundaryCharacteristic hp hp1 b φ) μ*
      sourceBracket h2p (sourceBoundaryTerminalDiscriminant hp hp1 b n)
        (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ =
      extensionSign b*sourceAntiDiscriminantCandidate hp hp1 φ μ*
        deriv (canonicalDiscriminant hp (periodOnePotential φ)) μ*periodOneBoundaryCharacteristic hp hp1 b φ w := by
  dsimp only
  rw [sourceBracket_boundaryTerminalDiscriminant_eq_fixed_and_root hp hp1 h2p b n φ hreal,
    sourceBracket_discriminants_eq_zero hp hp1 h2p φ]
  have h := sourceBoundaryRootDiscriminantBracket_mul hp hp1 h2p b φ hreal n w
  dsimp only [sourceBoundaryRootDiscriminantBracket] at h
  linear_combination deriv (canonicalDiscriminant hp (periodOnePotential φ))
    (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)*h

/-- The root-motion term cancels the other characteristic in the actual
moving anti-discriminant flow. No division by its possibly zero value is used. -/
theorem sourceBracket_boundaryTerminalAntiDiscriminant_discriminant_mul
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (w : ℂ) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    2*(μ-w)*deriv (periodOneBoundaryCharacteristic hp hp1 b φ) μ*
      sourceBracket h2p (sourceBoundaryTerminalAntiDiscriminant hp hp1 b n)
        (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ =
      extensionSign b*canonicalDiscriminant hp (periodOnePotential φ) μ*
        deriv (canonicalDiscriminant hp (periodOnePotential φ)) μ*periodOneBoundaryCharacteristic hp hp1 b φ w := by
  dsimp only
  rw [sourceBracket_boundaryTerminalAntiDiscriminant_eq_fixed_and_root hp hp1 h2p b n φ hreal]
  have hA := sourceBracket_anti_discriminant hp hp1 h2p φ (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) w
  have hR := sourceBoundaryRootDiscriminantBracket_mul hp hp1 h2p b φ hreal n w
  dsimp only [sourceBoundaryRootDiscriminantBracket] at hR
  have hS := sourceDiscriminant_mul_deriv_eq_anti_and_characteristics hp hp1 φ
    (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)
  have hχ := periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero hp hp1 b φ n
  cases b
  · simp only [extensionSign] at hR ⊢
    rw [hχ] at hA hS
    linear_combination
      2*deriv (periodOneBoundaryCharacteristic hp hp1 .dirichlet φ)
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n)*hA+
      deriv (sourceAntiDiscriminantCandidate hp hp1 φ)
        (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n)*hR-
      periodOneBoundaryCharacteristic hp hp1 .dirichlet φ w*hS
  · simp only [extensionSign] at hR ⊢
    rw [hχ] at hA hS
    linear_combination
      2*deriv (periodOneBoundaryCharacteristic hp hp1 .neumann φ)
        (canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ n)*hA+
      deriv (sourceAntiDiscriminantCandidate hp hp1 φ)
        (canonicalPeriodOneBoundaryRoots hp hp1 .neumann φ n)*hR+
      periodOneBoundaryCharacteristic hp hp1 .neumann φ w*hS

theorem sourceBracket_boundaryFloquetMultiplier_eq_terminals
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (G : CoeffPair p → ℂ) :
    sourceBracket h2p (sourceBoundaryFloquetMultiplier hp hp1 b n) G φ =
      (sourceBracket h2p (sourceBoundaryTerminalDiscriminant hp hp1 b n) G φ+
        extensionSign b*sourceBracket h2p (sourceBoundaryTerminalAntiDiscriminant hp hp1 b n) G φ)/2 := by
  have hD := (analyticAt_sourceBoundaryTerminalDiscriminant_of_realType hp hp1 b n φ hreal).differentiableAt
  have hA := (analyticAt_sourceBoundaryTerminalAntiDiscriminant_of_realType hp hp1 b n φ hreal).differentiableAt
  have hsum : DifferentiableAt ℂ (fun ψ : CoeffPair p =>
      sourceBoundaryTerminalDiscriminant hp hp1 b n ψ+
        extensionSign b*sourceBoundaryTerminalAntiDiscriminant hp hp1 b n ψ) φ :=
    hD.fun_add (hA.const_mul (extensionSign b))
  have hr : sourceBoundaryFloquetMultiplier hp hp1 b n =
      (fun ψ : CoeffPair p => (2 : ℂ)⁻¹*(sourceBoundaryTerminalDiscriminant hp hp1 b n ψ+
        extensionSign b*sourceBoundaryTerminalAntiDiscriminant hp hp1 b n ψ)) := by
    funext ψ
    simp only [sourceBoundaryFloquetMultiplier,div_eq_mul_inv]
    ring
  unfold sourceBracket
  rw [hr,fderiv_const_mul hsum (2 : ℂ)⁻¹,
    fderiv_fun_add hD (hA.const_mul (extensionSign b)),fderiv_const_mul hA (extensionSign b)]
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  ring

/-- The two boundary signs cancel in the signed actual multiplier flow.
The identity includes coincident parameters with the difference cleared. -/
theorem sourceBracket_boundaryFloquetMultiplier_discriminant_mul
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (w : ℂ) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    2*(μ-w)*deriv (periodOneBoundaryCharacteristic hp hp1 b φ) μ*
      sourceBracket h2p (sourceBoundaryFloquetMultiplier hp hp1 b n)
        (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ =
      sourceBoundaryFloquetMultiplier hp hp1 b n φ*
        deriv (canonicalDiscriminant hp (periodOnePotential φ)) μ*periodOneBoundaryCharacteristic hp hp1 b φ w := by
  dsimp only
  rw [sourceBracket_boundaryFloquetMultiplier_eq_terminals hp hp1 h2p b n φ hreal]
  have hD := sourceBracket_boundaryTerminalDiscriminant_discriminant_mul hp hp1 h2p b n φ hreal w
  have hA := sourceBracket_boundaryTerminalAntiDiscriminant_discriminant_mul hp hp1 h2p b n φ hreal w
  dsimp only at hD hA
  cases b
  · simp only [sourceBoundaryFloquetMultiplier,sourceBoundaryTerminalDiscriminant,
      sourceBoundaryTerminalAntiDiscriminant,extensionSign] at *
    linear_combination (1/2 : ℂ)*hD+(1/2 : ℂ)*hA
  · simp only [sourceBoundaryFloquetMultiplier,sourceBoundaryTerminalDiscriminant,
      sourceBoundaryTerminalAntiDiscriminant,extensionSign] at *
    linear_combination (1/2 : ℂ)*hD-(1/2 : ℂ)*hA

/-- The logarithmic multiplier bracket at distinct parameters is the
actual characteristic kernel, with no Floquet nonvanishing hypothesis. -/
theorem sourceBracket_boundaryFloquetMultiplier_discriminant_normalized
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (w : ℂ)
    (hw : canonicalPeriodOneBoundaryRoots hp hp1 b φ n ≠ w) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    sourceBracket h2p (sourceBoundaryFloquetMultiplier hp hp1 b n)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ/
        sourceBoundaryFloquetMultiplier hp hp1 b n φ =
      (deriv (canonicalDiscriminant hp (periodOnePotential φ)) μ*periodOneBoundaryCharacteristic hp hp1 b φ w)/
        (2*(μ-w)*deriv (periodOneBoundaryCharacteristic hp hp1 b φ) μ) := by
  dsimp only
  have hd := deriv_periodOneBoundaryCharacteristic_at_canonicalRoot_ne_zero_of_realType hp hp1 b φ hreal n
  have hρ := sourceBoundaryFloquetMultiplier_ne_zero hp hp1 b n φ
  have hf := sourceBracket_boundaryFloquetMultiplier_discriminant_mul hp hp1 h2p b n φ hreal w
  dsimp only at hf
  have hden : 2*(canonicalPeriodOneBoundaryRoots hp hp1 b φ n-w)*
      deriv (periodOneBoundaryCharacteristic hp hp1 b φ) (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hw)) hd
  have hb : sourceBracket h2p (sourceBoundaryFloquetMultiplier hp hp1 b n)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ =
        (sourceBoundaryFloquetMultiplier hp hp1 b n φ*
          deriv (canonicalDiscriminant hp (periodOnePotential φ)) (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)*
          periodOneBoundaryCharacteristic hp hp1 b φ w)/
            (2*(canonicalPeriodOneBoundaryRoots hp hp1 b φ n-w)*
              deriv (periodOneBoundaryCharacteristic hp hp1 b φ) (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)) := by
    apply (eq_div_iff hden).mpr
    rw [mul_comm]
    exact hf
  rw [hb]
  field_simp [hρ]

/-- The actual moving-multiplier bracket is entire in its discriminant
spectral argument, even at sources where a boundary coordinate is multiple. -/
theorem analyticOnNhd_sourceBracket_boundaryFloquetMultiplier_discriminant_spectral
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p) :
    AnalyticOnNhd ℂ (fun w : ℂ => sourceBracket h2p (sourceBoundaryFloquetMultiplier hp hp1 b n)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ) univ := by
  let L := sourceBivector h2p (fderiv ℂ (sourceBoundaryFloquetMultiplier hp hp1 b n) φ)
  intro w _
  have hc := ((analyticOnNhd_sourceDiscriminantCotangent_joint hp hp1) (w,φ) (mem_univ _)).comp
    (f := fun t : ℂ => (t,φ)) (analyticAt_id.prod analyticAt_const)
  exact (L.analyticAt _).comp hc

/-- At coincidence the normalized actual multiplier bracket is minus
one half the terminal spectral discriminant derivative. -/
theorem sourceBracket_boundaryFloquetMultiplier_discriminant_normalized_at_root
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    sourceBracket h2p (sourceBoundaryFloquetMultiplier hp hp1 b n)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) μ) φ/
        sourceBoundaryFloquetMultiplier hp hp1 b n φ =
      -deriv (canonicalDiscriminant hp (periodOnePotential φ)) μ/2 := by
  let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
  let d := deriv (periodOneBoundaryCharacteristic hp hp1 b φ) μ
  let ρ := sourceBoundaryFloquetMultiplier hp hp1 b n φ
  let t := deriv (canonicalDiscriminant hp (periodOnePotential φ)) μ
  let B : ℂ → ℂ := fun w => sourceBracket h2p (sourceBoundaryFloquetMultiplier hp hp1 b n)
    (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ
  have hB : DifferentiableAt ℂ B μ :=
    (analyticOnNhd_sourceBracket_boundaryFloquetMultiplier_discriminant_spectral
      hp hp1 h2p b n φ μ (mem_univ _)).differentiableAt
  have hχ := (analyticOnNhd_periodOneBoundaryCharacteristic hp hp1 b φ μ (mem_univ _)).differentiableAt.hasDerivAt
  have heq : (fun w : ℂ => 2*(μ-w)*(d*B w)) =
      (fun w => ρ*t*periodOneBoundaryCharacteristic hp hp1 b φ w) := by
    funext w
    have h := sourceBracket_boundaryFloquetMultiplier_discriminant_mul hp hp1 h2p b n φ hreal w
    dsimp only at h
    change 2*(μ-w)*(d*B w) = ρ*t*periodOneBoundaryCharacteristic hp hp1 b φ w
    linear_combination h
  have hl := (((hasDerivAt_const μ μ).sub (hasDerivAt_id μ)).const_mul (2 : ℂ)).mul
    (hB.hasDerivAt.const_mul d)
  change HasDerivAt (fun w : ℂ => 2*(μ-w)*(d*B w))
    (2*(0-1)*(d*B μ)+2*(μ-μ)*(d*deriv B μ)) μ at hl
  have hr := hχ.const_mul (ρ*t)
  rw [heq] at hl
  have hd := hl.unique hr
  simp only [sub_self,mul_zero,zero_mul,add_zero,zero_sub] at hd
  have hdn : d ≠ 0 :=
    deriv_periodOneBoundaryCharacteristic_at_canonicalRoot_ne_zero_of_realType hp hp1 b φ hreal n
  have hρ : ρ ≠ 0 := sourceBoundaryFloquetMultiplier_ne_zero hp hp1 b n φ
  have hb : B μ = -ρ*t/2 := by
    apply mul_left_cancel₀ hdn
    change 2*(-1)*(d*B μ) = ρ*t*d at hd
    linear_combination -(1/2 : ℂ)*hd
  change B μ/ρ = -t/2
  rw [hb]
  field_simp

end NLS.ZakharovShabat
