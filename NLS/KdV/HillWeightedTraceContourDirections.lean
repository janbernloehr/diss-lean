import NLS.KdV.HillAbelianCoordinateVariation
import NLS.KdV.HillActionHamiltonianDirections

/-! # Weighted physical trace directions on fixed energy contours

These are integrals of the actual Fourier Gardner directions. Their
isospectrality, weak Hamiltonian pairing, and action on the physical
coordinates follow from the proved pointwise trace laws. No frequency
formula or cotangent identification is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.KdV

def hillL2WeightedTraceContourDirection (p : Coeff 2) (a : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    Coeff 2 :=
  ∮ E in C(c,r), a E • hillL2DiscriminantGardnerDirection p E

theorem circleIntegrable_hillL2WeightedTraceContourDirection
    (q : RealPeriodOneHillPotential) (a : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hr : 0≤r) (ha : ContinuousOn a (sphere c r)) :
    CircleIntegrable (fun E => a E •
      hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q.val) E) c r :=
  (ha.smul (continuous_hillL2DiscriminantGardnerDirection_energy q).continuousOn).circleIntegrable hr

theorem apply_hillL2WeightedTraceContourDirection
    (q : RealPeriodOneHillPotential) (a : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hr : 0≤r) (ha : ContinuousOn a (sphere c r)) (L : Coeff 2 →L[ℂ] ℂ) :
    L (hillL2WeightedTraceContourDirection (SpectralWeight.one.toCoeff q.val) a c r) =
      ∮ E in C(c,r), a E * L
        (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q.val) E) := by
  rw [hillL2WeightedTraceContourDirection,map_circleIntegral L
    (circleIntegrable_hillL2WeightedTraceContourDirection q a c r hr ha)]
  simp only [map_smul,smul_eq_mul]

theorem fderiv_hillL2Discriminant_weightedTraceContourDirection
    (q : RealPeriodOneHillPotential) (a : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hr : 0≤r) (ha : ContinuousOn a (sphere c r)) (b : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p b) (SpectralWeight.one.toCoeff q.val))
      (hillL2WeightedTraceContourDirection (SpectralWeight.one.toCoeff q.val) a c r) = 0 := by
  rw [apply_hillL2WeightedTraceContourDirection q a c r hr ha]
  simp only [fderiv_hillL2Discriminant_gardnerDirection_eq_zero,mul_zero]
  simp [circleIntegral]

/-- The weak Gardner identity retains the integration-by-parts sign for
every continuous contour weight and every periodic AC test. -/
theorem hillPhysicalCurvePairing_weightedTraceContourDirection
    (q : RealPeriodOneHillPotential) (a : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hr : 0≤r) (ha : ContinuousOn a (sphere c r))
    (f g : Curve ℂ) (hf : AbsolutelyContinuousOnInterval (extend f) 0 1)
    (hfg : deriv (extend f)=ᵐ[volume.restrict (Ioc (0:ℝ) 1)] extend g)
    (hfend : extend f 0=extend f 1) (hgend : extend g 0=extend g 1) :
    hillPhysicalCurvePairing f
      (hillL2WeightedTraceContourDirection (SpectralWeight.one.toCoeff q.val) a c r) =
      -(∮ E in C(c,r), a E *
        (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E)
          (SpectralWeight.one.toCoeff q.val))
            (Coeff.periodDouble (NLS.Fourier.unitCurveCoefficientsCLM g))) := by
  rw [apply_hillL2WeightedTraceContourDirection q a c r hr ha]
  simp_rw [hillPhysicalCurvePairing_gardnerDirection_eq_neg_trace_derivative
    f g hf hfg hfend hgend,mul_neg]
  simp only [circleIntegral,smul_neg,intervalIntegral.integral_neg]

/-- Every matching differentiable physical coordinate obeys the same
weighted contour phase law, including when its selected gap is closed. -/
theorem fderiv_hillDirichletAbelianCoordinate_extension_weightedTraceContourDirection
    (q : RealPeriodOneHillPotential)
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (a : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0≤r) (ha : ContinuousOn a (sphere c r))
    (n : ℕ) (hn : 1≤n) (C : Coeff 2 → ℂ)
    (hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q.val))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      C (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn) :
    (fderiv ℂ C (SpectralWeight.one.toCoeff q.val))
      (hillL2WeightedTraceContourDirection (SpectralWeight.one.toCoeff q.val) a c r) =
      (-I/2*hillDirichletAbelianCoordinate q.val q.property.1 q.property.2 n hn) *
        ∮ E in C(c,r), a E*hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn E := by
  rw [apply_hillL2WeightedTraceContourDirection q a c r hr ha]
  simp_rw [fderiv_hillDirichletAbelianCoordinate_extension q.val q.property.1 q.property.2
    h0q h0r n hn C hC hmatch]
  rw [← circleIntegral.integral_const_mul]
  apply circleIntegral.integral_congr hr
  intro E _
  ring

end NLS.KdV
