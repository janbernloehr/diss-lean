import NLS.ZakharovShabat.SourceBoundaryTerminalPoisson
import NLS.ZakharovShabat.SourceBoundaryRootActionPoisson
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! # Actual local Floquet logarithm and action kernels

Dividing the moving multiplier by its nonzero base-source value gives one
at the base. The complex logarithm is therefore analytic locally at every
real-type source, including collapsed gaps. Its actual cotangent and
discriminant/action brackets require no logarithm-branch hypothesis.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An actual local logarithm normalized to zero at the selected source.
Only its local analyticity at that source is asserted. -/
def sourceBoundaryFloquetLogAt (hp : p ≠ ⊤) (hp1 : 1 < p)
    (b : BoundaryCondition) (n : ℤ) (φ ψ : CoeffPair p) : ℂ :=
  Complex.log (sourceBoundaryFloquetMultiplier hp hp1 b n ψ/
    sourceBoundaryFloquetMultiplier hp hp1 b n φ)

@[simp] theorem sourceBoundaryFloquetLogAt_self
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p) :
    sourceBoundaryFloquetLogAt hp hp1 b n φ φ = 0 := by
  simp [sourceBoundaryFloquetLogAt,sourceBoundaryFloquetMultiplier_ne_zero hp hp1 b n φ]

theorem analyticAt_sourceBoundaryFloquetLogAt_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    AnalyticAt ℂ (sourceBoundaryFloquetLogAt hp hp1 b n φ) φ := by
  have hρ := sourceBoundaryFloquetMultiplier_ne_zero hp hp1 b n φ
  exact (analyticAt_sourceBoundaryFloquetMultiplier_of_realType hp hp1 b n φ hreal).div_const.clog
    (by simpa only [div_self hρ] using one_mem_slitPlane)

/-- The full actual local logarithm differential is the multiplier
cotangent divided by its value; nonvanishing is already proved globally. -/
theorem fderiv_sourceBoundaryFloquetLogAt
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (n : ℤ)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    fderiv ℂ (sourceBoundaryFloquetLogAt hp hp1 b n φ) φ =
      (sourceBoundaryFloquetMultiplier hp hp1 b n φ)⁻¹ •
        fderiv ℂ (sourceBoundaryFloquetMultiplier hp hp1 b n) φ := by
  have hρ := sourceBoundaryFloquetMultiplier_ne_zero hp hp1 b n φ
  have hd := (analyticAt_sourceBoundaryFloquetMultiplier_of_realType hp hp1 b n φ hreal).differentiableAt
  have hn : HasFDerivAt (fun ψ : CoeffPair p => sourceBoundaryFloquetMultiplier hp hp1 b n ψ/
      sourceBoundaryFloquetMultiplier hp hp1 b n φ)
      ((sourceBoundaryFloquetMultiplier hp hp1 b n φ)⁻¹ •
        fderiv ℂ (sourceBoundaryFloquetMultiplier hp hp1 b n) φ) φ := by
    simpa only [div_eq_mul_inv] using!
      hd.hasFDerivAt.mul_const (sourceBoundaryFloquetMultiplier hp hp1 b n φ)⁻¹
  have hl := hn.clog (by simpa only [div_self hρ] using one_mem_slitPlane)
  simpa only [sourceBoundaryFloquetLogAt,div_self hρ,inv_one,one_smul] using! hl.fderiv

/-- This is a bracket of an actual analytic local logarithm, rather than
an assumed logarithmic derivative or an externally supplied branch. -/
theorem sourceBracket_boundaryFloquetLogAt_eq_normalized
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (G : CoeffPair p → ℂ) :
    sourceBracket h2p (sourceBoundaryFloquetLogAt hp hp1 b n φ) G φ =
      sourceBracket h2p (sourceBoundaryFloquetMultiplier hp hp1 b n) G φ/
        sourceBoundaryFloquetMultiplier hp hp1 b n φ := by
  unfold sourceBracket
  rw [fderiv_sourceBoundaryFloquetLogAt hp hp1 b n φ hreal]
  simp only [map_smul,smul_apply,smul_eq_mul,div_eq_mul_inv]
  ring

/-- The literal characteristic kernel for the actual moving-terminal
local logarithm and a fixed-parameter discriminant. -/
theorem sourceBracket_boundaryFloquetLogAt_discriminant_eq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (w : ℂ)
    (hw : canonicalPeriodOneBoundaryRoots hp hp1 b φ n ≠ w) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    sourceBracket h2p (sourceBoundaryFloquetLogAt hp hp1 b n φ)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ =
      (deriv (canonicalDiscriminant hp (periodOnePotential φ)) μ*periodOneBoundaryCharacteristic hp hp1 b φ w)/
        (2*(μ-w)*deriv (periodOneBoundaryCharacteristic hp hp1 b φ) μ) := by
  dsimp only
  rw [sourceBracket_boundaryFloquetLogAt_eq_normalized hp hp1 h2p b n φ hreal]
  exact sourceBracket_boundaryFloquetMultiplier_discriminant_normalized hp hp1 h2p b n φ hreal w hw

/-- The apparent spectral pole is removable at the actual terminal. -/
theorem sourceBracket_boundaryFloquetLogAt_discriminant_at_root
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n : ℤ) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    sourceBracket h2p (sourceBoundaryFloquetLogAt hp hp1 b n φ)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) μ) φ =
        -deriv (canonicalDiscriminant hp (periodOnePotential φ)) μ/2 := by
  dsimp only
  rw [sourceBracket_boundaryFloquetLogAt_eq_normalized hp hp1 h2p b n φ hreal]
  exact sourceBracket_boundaryFloquetMultiplier_discriminant_normalized_at_root hp hp1 h2p b n φ hreal

/-- Passing the actual action cotangent through the source bivector gives
a contour of the actual local logarithm/discriminant bracket. -/
theorem sourceBracket_boundaryFloquetLogAt_action_eq_discriminant_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n m : ℤ) (ch : SourceRealActionBallChart hp hp1 m)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hφ : φ ∈ ball ch.center ch.radius) :
    sourceBracket h2p (sourceBoundaryFloquetLogAt hp hp1 b n φ) (sourceComplexAction hp hp1 m) φ =
      -(Real.pi : ℂ)⁻¹*(∮ w in C(ch.spectralCenter,ch.spectralRadius),
        (sourceCanonicalRoot hp hp1 φ w)⁻¹*sourceBracket h2p (sourceBoundaryFloquetLogAt hp hp1 b n φ)
          (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ) := by
  have hgeom := ch.geometry φ hφ
  have hcircle := sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ m
    ch.spectralCenter ch.spectralRadius hgeom.1 hgeom.2
  have hint := circleIntegrable_sourceActionVariationCotangent hp hp1 φ
    ch.spectralCenter ch.spectralRadius ch.spectralRadius_pos.le hcircle
  rw [sourceBracket,fderiv_sourceComplexAction_eq_cotangent_circle_on_chart hp hp1 m ch φ hreal hφ]
  simp only [map_smul,smul_eq_mul]
  rw [NLS.ComplexAnalysis.map_circleIntegral
    (sourceBivector h2p (fderiv ℂ (sourceBoundaryFloquetLogAt hp hp1 b n φ) φ)) hint]
  congr 1
  apply circleIntegral.integral_congr ch.spectralRadius_pos.le
  intro w _
  dsimp only
  simp only [sourceActionVariationCotangent,sourceDiscriminantCotangent,sourceBracket,
    map_smul,smul_eq_mul]

/-- Real interlacing makes every action circle avoid the moving boundary
terminal, so its actual logarithmic action kernel needs no avoidance or
open-gap hypothesis. Both ordinary boundary families have this sign. -/
theorem sourceBracket_boundaryFloquetLogAt_action_eq_characteristic_circle
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (b : BoundaryCondition) (n m : ℤ) (ch : SourceRealActionBallChart hp hp1 m)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (hφ : φ ∈ ball ch.center ch.radius) :
    let μ := canonicalPeriodOneBoundaryRoots hp hp1 b φ n
    sourceBracket h2p (sourceBoundaryFloquetLogAt hp hp1 b n φ) (sourceComplexAction hp hp1 m) φ =
      -(Real.pi : ℂ)⁻¹*(∮ w in C(ch.spectralCenter,ch.spectralRadius),
        (sourceCanonicalRoot hp hp1 φ w)⁻¹*
          (deriv (canonicalDiscriminant hp (periodOnePotential φ)) μ*periodOneBoundaryCharacteristic hp hp1 b φ w)/
            (2*(μ-w)*deriv (periodOneBoundaryCharacteristic hp hp1 b φ) μ)) := by
  dsimp only
  rw [sourceBracket_boundaryFloquetLogAt_action_eq_discriminant_circle hp hp1 h2p b n m ch φ hreal hφ]
  have hgeom := ch.geometry φ hφ
  have hcircle := sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ m
    ch.spectralCenter ch.spectralRadius hgeom.1 hgeom.2
  congr 1
  apply circleIntegral.integral_congr ch.spectralRadius_pos.le
  intro w hw
  dsimp only
  rw [sourceBracket_boundaryFloquetLogAt_discriminant_eq hp hp1 h2p b n φ hreal w
    (canonicalPeriodOneBoundaryRoot_ne_of_sourceCanonicalRootDomain hp hp1 b φ hreal n w (hcircle hw))]
  ring

end NLS.ZakharovShabat
