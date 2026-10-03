import NLS.ZakharovShabat.SourceBoundarySimpleNeighborhood
import NLS.ComplexAnalysis.MovingSpectralParameter

/-! # Canonical boundary root differentials at complex simple sources

The actual zero equation determines the derivative on the common simple
root domain, without a real-type assumption.
-/

noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The implicit characteristic quotient is the full actual root cotangent
at any differentiable simple canonical root, including complex sources. -/
theorem fderiv_canonicalPeriodOneBoundaryRoot_eq_cotangent_of_simple
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (φ : CoeffPair p) (n : ℤ)
    (hμ : DifferentiableAt ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ)
    (hs : deriv (periodOneBoundaryCharacteristic hp hp1 b φ) (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) ≠ 0) :
    fderiv ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ =
      -(deriv (periodOneBoundaryCharacteristic hp hp1 b φ) (canonicalPeriodOneBoundaryRoots hp hp1 b φ n))⁻¹ •
        sourceBoundaryCharacteristicCotangent hp hp1 b (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) φ := by
  let μ : CoeffPair p → ℂ := fun ψ => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n
  let F : ℂ × CoeffPair p → ℂ := fun t => periodOneBoundaryCharacteristic hp hp1 b t.2 t.1
  have hF := (analyticOnNhd_periodOneBoundaryCharacteristic_joint hp hp1 b (μ φ,φ) (mem_univ _)).differentiableAt
  have he : (fun ψ : CoeffPair p => F (μ ψ,ψ)) = (fun _ => (0 : ℂ)) :=
    funext (fun ψ => periodOneBoundaryCharacteristic_at_canonicalRoot_eq_zero hp hp1 b ψ n)
  have hc := fderiv_moving_spectral_parameter F μ φ hF hμ
  rw [he] at hc
  simp only [fderiv_const_apply] at hc
  apply ContinuousLinearMap.ext
  intro h
  have hh := congrArg (fun L : CoeffPair p →L[ℂ] ℂ => L h) hc
  change 0 = sourceBoundaryCharacteristicCotangent hp hp1 b (μ φ) φ h+
    deriv (periodOneBoundaryCharacteristic hp hp1 b φ) (μ φ)*(fderiv ℂ μ φ) h at hh
  change (fderiv ℂ μ φ) h = -(deriv (periodOneBoundaryCharacteristic hp hp1 b φ) (μ φ))⁻¹*
    sourceBoundaryCharacteristicCotangent hp hp1 b (μ φ) φ h
  have hs' : deriv (periodOneBoundaryCharacteristic hp hp1 b φ) (μ φ) ≠ 0 := hs
  field_simp [hs']
  linear_combination -hh

end NLS.ZakharovShabat
