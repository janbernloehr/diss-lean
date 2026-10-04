import NLS.ZakharovShabat.SourceGapCosineMeanBound
import NLS.ZakharovShabat.SourceStandardRootGapSidePolynomial

/-! # Exact leading cosine terms on complex gaps

The polynomial model gives the diagonal coefficient pi times the squared
gap divided by four. A shifted linear factor leaves only its displacement
from the midpoint. Both formulas include collapsed complex gaps.
-/
noncomputable section
open Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The quadratic cosine average is valid for every complex half-gap. -/
theorem cosineIntegral_quadratic (τ δ : ℂ) :
    (∫ θ in (0:ℝ)..Real.pi, (τ+δ*(Real.cos θ:ℂ)-τ)^2-δ^2) =
      -(Real.pi:ℂ)*δ^2/2 := by
  by_cases hδ : δ = 0
  · simp [hδ]
  have h := gapSideBoundaryIntegral_quadratic τ δ true
  rw [gapSideBoundaryIntegral_eq_primitive τ δ _ 1 hδ true] at h
  simp only [gapSidePrimitive,Real.arccos_one,ite_true] at h
  apply mul_left_cancel₀ Complex.I_ne_zero
  calc
    Complex.I * _ = _ := h
    _ = Complex.I * (-(Real.pi:ℂ)*δ^2/2) := by ring

/-- The odd centered contribution cancels for complex as well as real gaps. -/
theorem cosineIntegral_shifted_quadratic (τ δ sigma : ℂ) :
    (∫ θ in (0:ℝ)..Real.pi,
      (sigma-(τ+δ*(Real.cos θ:ℂ)))*((τ+δ*(Real.cos θ:ℂ)-τ)^2-δ^2)) =
      -(Real.pi:ℂ)*δ^2*(sigma-τ)/2 := by
  by_cases hδ : δ = 0
  · simp [hδ]
  have h := gapSideBoundaryIntegral_shifted_quadratic τ δ sigma true
  rw [gapSideBoundaryIntegral_eq_primitive τ δ _ 1 hδ true] at h
  simp only [gapSidePrimitive,Real.arccos_one,ite_true] at h
  apply mul_left_cancel₀ Complex.I_ne_zero
  calc
    Complex.I * _ = _ := h
    _ = Complex.I * (-(Real.pi:ℂ)*δ^2*(sigma-τ)/2) := by ring

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The diagonal model has exactly the leading coefficient in Lemma 20.3,
without any real-source or nonzero-gap assumption. -/
theorem sourceGapCosineMean_diagonal_model
    (hp : p ≠ ⊤) (hp1 : 1 < p) (k : ℤ) (ψ : CoeffPair p) :
    -(2*Complex.I) * sourceGapCosineMean hp hp1 k (fun t : ℂ × CoeffPair p =>
      -Complex.I * ((t.1-sourceStandardRootMidpoint hp hp1 t.2 k)^2-
        (sourceStandardRootHalfGap hp hp1 t.2 k)^2)) ψ =
      (Real.pi:ℂ) * (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k)^2 / 4 := by
  unfold sourceGapCosineMean parametricCosineMean
  dsimp only
  rw [intervalIntegral.integral_const_mul,cosineIntegral_quadratic]
  unfold sourceStandardRootHalfGap
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The shifted model leaves only the root displacement from the gap
midpoint, the cancellation responsible for the extra off-diagonal decay. -/
theorem sourceGapCosineMean_shifted_model
    (hp : p ≠ ⊤) (hp1 : 1 < p) (k : ℤ) (ψ : CoeffPair p) (sigma : ℂ) :
    -(2*Complex.I) * sourceGapCosineMean hp hp1 k (fun t : ℂ × CoeffPair p =>
      -Complex.I * ((sigma-t.1) * ((t.1-sourceStandardRootMidpoint hp hp1 t.2 k)^2-
        (sourceStandardRootHalfGap hp hp1 t.2 k)^2))) ψ =
      (Real.pi:ℂ) * (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) k)^2 *
        (sigma-sourceStandardRootMidpoint hp hp1 ψ k) / 4 := by
  unfold sourceGapCosineMean parametricCosineMean
  dsimp only
  rw [intervalIntegral.integral_const_mul,cosineIntegral_shifted_quadratic]
  unfold sourceStandardRootHalfGap
  ring_nf
  simp only [Complex.I_sq]
  ring

end NLS.ZakharovShabat
