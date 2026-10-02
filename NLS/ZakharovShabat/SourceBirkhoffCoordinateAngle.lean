import NLS.ZakharovShabat.SourceBirkhoffCoordinates
import NLS.ZakharovShabat.SourceAngularThetaAnalytic

/-! # Agreement with the open-gap rectangular angle formulas

Formula (3.2) recovers (3.1) on every actual eta chart with the
canonical half-gap. The `y` coordinate uses the difference of the
signed phases, giving the sine with the positive stated orientation.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourceAngularEtaAnalyticChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {n : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V U : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ}
  {r R : ℝ} {z₀ : ℂ} {ρ : ℝ} {δ ε : CoeffPair p → ℂ}

/-- The full signed phase is the original eta-plus-beta angle. -/
theorem birkhoffWeightedCoordinate_eq_gap_exp
    (D : SourceAngularEtaAnalyticChartData hp hp1 n s W V U c T r R z₀ ρ δ ε)
    (ψ : CoeffPair p) (hψ : ψ ∈ U) (sign : ℂ) (hsign : sign = 1 ∨ sign = -1)
    (hδ : δ ψ = canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n/2) :
    sourceBirkhoffWeightedCoordinate hp hp1 n s sign ψ =
      sourceNormalizedActionRoot hp hp1 n ψ * sourcePeriodicGapDisplacement hp hp1 ψ n *
        Complex.exp (sign*I*sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε ψ) := by
  rw [sourceBirkhoffWeightedCoordinate,D.gapWeightedEtaCoordinate_eq_gap_exp ψ hψ sign hsign hδ,
    sourceAngularThetaCauchyRepresentative,mul_add,Complex.exp_add,sourcePeriodicGapDisplacement_apply]
  ring

/-- Formula (3.1), with the actual full theta representative and
canonical periodic gap, follows from the extended coordinates. -/
theorem birkhoffXY_eq_gap_cos_sin
    (D : SourceAngularEtaAnalyticChartData hp hp1 n s W V U c T r R z₀ ρ δ ε)
    (ψ : CoeffPair p) (hψ : ψ ∈ U)
    (hδ : δ ψ = canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n/2) :
    let θ := sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε ψ
    let a := sourceNormalizedActionRoot hp hp1 n ψ * sourcePeriodicGapDisplacement hp hp1 ψ n / (Real.sqrt 2 : ℂ)
    sourceBirkhoffX hp hp1 n s ψ = a*Complex.cos θ ∧
      sourceBirkhoffY hp hp1 n s ψ = a*Complex.sin θ := by
  dsimp only
  let θ := sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε ψ
  have h8 : (Real.sqrt 8 : ℂ) = 2*(Real.sqrt 2 : ℂ) := by
    have h : Real.sqrt 8 = 2*Real.sqrt 2 := by
      rw [show (8:ℝ) = 4*2 by norm_num,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
      rw [show (4:ℝ) = 2^2 by norm_num,Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    exact_mod_cast h
  have hplus : Complex.exp (I*θ) = Complex.cos θ+Complex.sin θ*I := by
    rw [mul_comm,Complex.exp_mul_I]
  have hminus : Complex.exp (-1*I*θ) = Complex.cos θ-Complex.sin θ*I := by
    rw [show -1*I*θ = -θ*I by ring,← Complex.cos_sub_sin_I]
  rw [sourceBirkhoffX,sourceBirkhoffY,
    D.birkhoffWeightedCoordinate_eq_gap_exp ψ hψ 1 (Or.inl rfl) hδ,
    D.birkhoffWeightedCoordinate_eq_gap_exp ψ hψ (-1) (Or.inr rfl) hδ]
  simp only [one_mul]
  change (_*Complex.exp (I*θ)+_*Complex.exp (-1*I*θ))/(Real.sqrt 8 : ℂ) = _ ∧
    (_*Complex.exp (I*θ)-_*Complex.exp (-1*I*θ))/((Real.sqrt 8 : ℂ)*I) = _
  rw [hplus,hminus,h8]
  constructor
  · ring
  · simp only [div_eq_mul_inv,mul_inv_rev,inv_I]
    calc
      _ = (sourceNormalizedActionRoot hp hp1 n ψ * sourcePeriodicGapDisplacement hp hp1 ψ n /
        (Real.sqrt 2 : ℂ))*Complex.sin θ*(-I^2) := by ring
      _ = _ := by rw [I_sq]; ring

end SourceAngularEtaAnalyticChartData
end NLS.ZakharovShabat
