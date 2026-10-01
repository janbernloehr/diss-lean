import NLS.ZakharovShabat.SourceAntiSpectralPoisson
import NLS.ZakharovShabat.SourceSeparatedPoisson
import NLS.ZakharovShabat.SourceBoundaryFloquetLogActionPoisson

/-! # Actual mixed root/Floquet logarithm separation brackets

The characteristic/anti-discriminant flow gives the missing actual
root/anti-discriminant bracket. Root involution removes the moving
terminal correction in a mixed root/multiplier bracket. Distinct indexed
roots give zero, while coincidence gives minus one half after logarithmic
normalization. Both ordinary boundary families and collapsed gaps are included.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
open BoundaryCondition
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def sourceBoundaryRootAntiDiscriminantBracket
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p) (n : ℤ) (w : ℂ) : ℂ :=
  sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n)
    (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ w) φ

theorem sourceBoundaryRootAntiDiscriminantBracket_mul
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (w : ℂ) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    2*(μ-w)*(deriv (periodOneBoundaryCharacteristic hp hp1 b φ) μ*
      sourceBoundaryRootAntiDiscriminantBracket hp hp1 h2p b φ n w) =
        extensionSign b*canonicalDiscriminant hp (periodOnePotential φ) μ*
          periodOneBoundaryCharacteristic hp hp1 b φ w := by
  dsimp only
  rw [sourceBoundaryRootAntiDiscriminantBracket,sourceBracket_boundaryRoot_balance hp hp1 h2p b φ hreal n]
  have h := sourceBracket_boundary_anti hp hp1 h2p b φ (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) w
  rw [periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero hp hp1 b φ n] at h
  linear_combination -h

theorem sourceBoundaryRootAntiDiscriminantBracket_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (w : ℂ)
    (hw : canonicalPeriodOneBoundaryRoots hp hp1 b φ n ≠ w) :
    sourceBoundaryRootAntiDiscriminantBracket hp hp1 h2p b φ n w =
      (extensionSign b*canonicalDiscriminant hp (periodOnePotential φ) (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)*
        periodOneBoundaryCharacteristic hp hp1 b φ w)/
        (2*(canonicalPeriodOneBoundaryRoots hp hp1 b φ n-w)*
          deriv (periodOneBoundaryCharacteristic hp hp1 b φ) (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)) := by
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) (sub_ne_zero.mpr hw))
    (deriv_periodOneBoundaryCharacteristic_at_canonicalRoot_ne_zero_of_realType hp hp1 b φ hreal n))).mpr
  have h := sourceBoundaryRootAntiDiscriminantBracket_mul hp hp1 h2p b φ hreal n w
  dsimp only at h
  linear_combination h

/-- The actual coincident root/anti-discriminant bracket is minus half
the signed terminal discriminant, even when the periodic gap collapses. -/
theorem sourceBoundaryRootAntiDiscriminantBracket_at_root
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    sourceBoundaryRootAntiDiscriminantBracket hp hp1 h2p b φ n (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) =
      -extensionSign b*canonicalDiscriminant hp (periodOnePotential φ) (canonicalPeriodOneBoundaryRoots hp hp1 b φ n)/2 := by
  rw [sourceBoundaryRootAntiDiscriminantBracket,sourceBracket_boundaryRoot_eq_characteristic hp hp1 h2p b φ hreal n,
    sourceBracket_boundary_anti_diagonal,periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero hp hp1 b φ n]
  have hd := deriv_periodOneBoundaryCharacteristic_at_canonicalRoot_ne_zero_of_realType hp hp1 b φ hreal n
  field_simp
  ring

/-- Since the actual roots commute within their family, moving the second
terminal contributes zero to this mixed root/multiplier bracket. -/
theorem sourceBracket_boundaryRoot_floquet_eq_fixed
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n m : ℤ) :
    let ν := canonicalPeriodOneBoundaryRoots hp hp1 b φ m
    sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n)
      (sourceBoundaryFloquetMultiplier hp hp1 b m) φ =
      (sourceBoundaryRootDiscriminantBracket hp hp1 h2p b φ n ν+
        extensionSign b*sourceBoundaryRootAntiDiscriminantBracket hp hp1 h2p b φ n ν)/2 := by
  dsimp only
  let μn : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n
  have hD := sourceBracket_boundaryTerminalDiscriminant_eq_fixed_and_root hp hp1 h2p b m φ hreal μn
  have hA := sourceBracket_boundaryTerminalAntiDiscriminant_eq_fixed_and_root hp hp1 h2p b m φ hreal μn
  dsimp only at hD hA
  have hroots : sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ m) μn φ = 0 :=
    sourceBracket_boundaryRoots_eq_zero hp hp1 h2p b φ hreal m n
  rw [hroots,mul_zero,add_zero] at hD hA
  have hρ := sourceBracket_boundaryFloquetMultiplier_eq_terminals hp hp1 h2p b m φ hreal μn
  rw [hD,hA,sourceBracket_antisymm h2p (sourceBoundaryFloquetMultiplier hp hp1 b m) μn φ,
    sourceBracket_antisymm h2p (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ)
      (canonicalPeriodOneBoundaryRoots hp hp1 b φ m)) μn φ,
    sourceBracket_antisymm h2p (fun ψ : CoeffPair p => sourceAntiDiscriminantCandidate hp hp1 ψ
      (canonicalPeriodOneBoundaryRoots hp hp1 b φ m)) μn φ] at hρ
  change -sourceBracket h2p μn (sourceBoundaryFloquetMultiplier hp hp1 b m) φ =
    (-sourceBoundaryRootDiscriminantBracket hp hp1 h2p b φ n (canonicalPeriodOneBoundaryRoots hp hp1 b φ m)+
      extensionSign b*(-sourceBoundaryRootAntiDiscriminantBracket hp hp1 h2p b φ n (canonicalPeriodOneBoundaryRoots hp hp1 b φ m)))/2 at hρ
  linear_combination -hρ

theorem sourceBracket_boundaryRoot_floquet_diagonal
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n)
      (sourceBoundaryFloquetMultiplier hp hp1 b n) φ = -sourceBoundaryFloquetMultiplier hp hp1 b n φ/2 := by
  rw [sourceBracket_boundaryRoot_floquet_eq_fixed hp hp1 h2p b φ hreal,
    sourceBoundaryRootDiscriminantBracket_at_root hp hp1 h2p b φ hreal,
    sourceBoundaryRootAntiDiscriminantBracket_at_root hp hp1 h2p b φ hreal]
  simp only [sourceBoundaryFloquetMultiplier,sourceBoundaryTerminalDiscriminant,sourceBoundaryTerminalAntiDiscriminant]
  cases b <;> simp only [extensionSign] <;> ring

theorem sourceBracket_boundaryRoot_floquet_off_diagonal
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n m : ℤ) (hnm : n ≠ m) :
    sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n)
      (sourceBoundaryFloquetMultiplier hp hp1 b m) φ = 0 := by
  have hμ : canonicalPeriodOneBoundaryRoots hp hp1 b φ n ≠ canonicalPeriodOneBoundaryRoots hp hp1 b φ m :=
    (injective_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 b φ hreal).ne hnm
  rw [sourceBracket_boundaryRoot_floquet_eq_fixed hp hp1 h2p b φ hreal,
    sourceBoundaryRootDiscriminantBracket_eq hp hp1 h2p b φ hreal n _ hμ,
    sourceBoundaryRootAntiDiscriminantBracket_eq hp hp1 h2p b φ hreal n _ hμ,
    periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero hp hp1 b φ m]
  simp

theorem sourceBracket_right_boundaryFloquetLogAt_eq_normalized
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (m : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (F : CoeffPair p → ℂ) :
    sourceBracket h2p F (sourceBoundaryFloquetLogAt hp hp1 b m φ) φ =
      sourceBracket h2p F (sourceBoundaryFloquetMultiplier hp hp1 b m) φ/
        sourceBoundaryFloquetMultiplier hp hp1 b m φ := by
  rw [sourceBracket_antisymm,sourceBracket_boundaryFloquetLogAt_eq_normalized hp hp1 h2p b m φ hreal,
    sourceBracket_antisymm]
  ring

/-- The actual mixed separation relation for every real source and all
indices, including central indices and collapsed periodic gaps. The
factor minus one half is fixed by the original period-one normalization. -/
theorem sourceBracket_boundaryRoot_floquetLog_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (n m : ℤ) :
    sourceBracket h2p (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n)
      (sourceBoundaryFloquetLogAt hp hp1 b m φ) φ = if n = m then -(1 : ℂ)/2 else 0 := by
  rw [sourceBracket_right_boundaryFloquetLogAt_eq_normalized hp hp1 h2p b m φ hreal]
  by_cases hnm : n = m
  · subst m
    rw [if_pos rfl,sourceBracket_boundaryRoot_floquet_diagonal hp hp1 h2p b φ hreal]
    have hρ := sourceBoundaryFloquetMultiplier_ne_zero hp hp1 b n φ
    field_simp
  · rw [if_neg hnm,sourceBracket_boundaryRoot_floquet_off_diagonal hp hp1 h2p b φ hreal n m hnm]
    simp

end NLS.ZakharovShabat
