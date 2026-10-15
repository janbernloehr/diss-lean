import NLS.ZakharovShabat.SourceGapWeightedEtaOriginal
import NLS.ZakharovShabat.SourceBirkhoffCoordinates

/-!
# Equation (3.1) for the original theta sum

The weighted coordinates and rectangular cosine/sine formulas use
the literal original eta-plus-beta angle, with its exact orientation.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The exact weighted coordinate is the literal original theta phase. -/
theorem birkhoffWeighted_original_formula (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0)
    (sign : ℂ) (hsign : sign = 1 ∨ sign = -1) :
    sourceBirkhoffWeightedCoordinate hp hp1 n s sign ψ =
      sourceNormalizedActionRoot hp hp1 n ψ *
        canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n *
        Complex.exp (sign*Complex.I*sourceAngularOriginalTheta hp hp1 n s ψ) := by
  rw [sourceBirkhoffWeightedCoordinate,H.gapWeightedEta_original_signed ψ hψ n hgap sign hsign,
    sourceAngularOriginalTheta,mul_add,Complex.exp_add]
  ring

/-- Formula (3.1) uses the actual original angles with no sign ambiguity. -/
theorem birkhoffXY_original_formula (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0) :
    let θ := sourceAngularOriginalTheta hp hp1 n s ψ
    let a := sourceNormalizedActionRoot hp hp1 n ψ * (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) / (Real.sqrt 2 : ℂ)
    sourceBirkhoffX hp hp1 n s ψ = a*Complex.cos θ ∧
      sourceBirkhoffY hp hp1 n s ψ = a*Complex.sin θ := by
  dsimp only
  let θ := sourceAngularOriginalTheta hp hp1 n s ψ
  have h8 : (Real.sqrt 8 : ℂ) = 2*(Real.sqrt 2 : ℂ) := by
    have h : Real.sqrt 8 = 2*Real.sqrt 2 := by
      rw [show (8:ℝ) = 4*2 by norm_num,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
      rw [show (4:ℝ) = 2^2 by norm_num,Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    exact_mod_cast h
  have hplus : Complex.exp (Complex.I*θ) = Complex.cos θ+Complex.sin θ*Complex.I := by
    rw [mul_comm,Complex.exp_mul_I]
  have hminus : Complex.exp (-1*Complex.I*θ) = Complex.cos θ-Complex.sin θ*Complex.I := by
    rw [show -1*Complex.I*θ = -θ*Complex.I by ring,← Complex.cos_sub_sin_I]
  rw [sourceBirkhoffX,sourceBirkhoffY,
    H.birkhoffWeighted_original_formula ψ hψ n hgap 1 (Or.inl rfl),
    H.birkhoffWeighted_original_formula ψ hψ n hgap (-1) (Or.inr rfl)]
  simp only [one_mul]
  change (_*Complex.exp (Complex.I*θ)+_*Complex.exp (-1*Complex.I*θ))/(Real.sqrt 8 : ℂ) = _ ∧
    (_*Complex.exp (Complex.I*θ)-_*Complex.exp (-1*Complex.I*θ))/((Real.sqrt 8 : ℂ)*Complex.I) = _
  rw [hplus,hminus,h8]
  constructor
  · ring
  · simp only [div_eq_mul_inv,mul_inv_rev,inv_I]
    calc
      _ = (sourceNormalizedActionRoot hp hp1 n ψ * (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n) /
        (Real.sqrt 2 : ℂ))*Complex.sin θ*(-Complex.I^2) := by ring
      _ = _ := by rw [I_sq]; ring



end SourceLemma12_12Data
end NLS.ZakharovShabat
