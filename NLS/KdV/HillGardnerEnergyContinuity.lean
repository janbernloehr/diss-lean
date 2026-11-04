import NLS.KdV.HillL2GardnerDirections
import NLS.KdV.HillRealPeriodOneTruncation
import NLS.Fourier.UnitCurveCoefficients
import Mathlib.Topology.Algebra.Polynomial

/-! # Energy continuity of the actual L2 Gardner directions -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.Fourier
namespace NLS.KdV

/-- The scalar physical trace gradient depends on the squared frequency.
The equality is proved by continuous rough-source approximation. -/
theorem hillL2TraceGradientSpatialCurve_eq_of_sq_eq
    (q : RealPeriodOneHillPotential) (z w : ℂ) (he : z^2=w^2) :
    hillL2TraceGradientSpatialCurve (SpectralWeight.one.toCoeff q.val) z =
      hillL2TraceGradientSpatialCurve (SpectralWeight.one.toCoeff q.val) w := by
  let P : RealPeriodOneHillPotential → Coeff 2 := fun p => SpectralWeight.one.toCoeff p.val
  have hP : Continuous P := SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val
  have hfinite (N : ℕ) : hillL2TraceGradientSpatialCurve (P (hillRealPeriodOneTruncate N q)) z =
      hillL2TraceGradientSpatialCurve (P (hillRealPeriodOneTruncate N q)) w := by
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) (hillRealPeriodOneTruncationFinsupp N q))
    have hQ : hillContinuousCoefficients Q=(hillRealPeriodOneTruncate N q).val :=
      hillContinuousCoefficients_realPeriodOneTruncation N q
    change hillL2TraceGradientSpatialCurve (SpectralWeight.one.toCoeff (hillRealPeriodOneTruncate N q).val) z = _
    dsimp only [P]
    rw [← hQ]
    ext t
    rw [hillL2TraceGradientSpatialCurve_eq_classical,hillL2TraceGradientSpatialCurve_eq_classical,he]
  have hz := ((continuous_hillL2TraceGradientSpatialCurve z).comp hP).continuousAt.tendsto.comp
    (tendsto_hillRealPeriodOneTruncate q)
  have hw := ((continuous_hillL2TraceGradientSpatialCurve w).comp hP).continuousAt.tendsto.comp
    (tendsto_hillRealPeriodOneTruncate q)
  exact tendsto_nhds_unique hz (hw.congr' (Eventually.of_forall (fun N => (hfinite N).symm)))

/-- The principal square-root cut introduces no discontinuity in the
actual energy-dependent physical trace-gradient curve, including at zero. -/
theorem continuous_hillL2TraceGradientSpatialCurve_energy (q : RealPeriodOneHillPotential) :
    Continuous (fun E : ℂ => hillL2TraceGradientSpatialCurve (SpectralWeight.one.toCoeff q.val) (Complex.sqrt E)) := by
  have hsurj : Function.Surjective (fun z : ℂ => z^2) := fun E => ⟨Complex.sqrt E,complex_sqrt_sq E⟩
  apply ((isClosedMap_pow ℂ 2).isQuotientMap (continuous_pow 2) hsurj).continuous_iff.mpr
  have he (z : ℂ) : hillL2TraceGradientSpatialCurve (SpectralWeight.one.toCoeff q.val) (Complex.sqrt (z^2)) =
      hillL2TraceGradientSpatialCurve (SpectralWeight.one.toCoeff q.val) z :=
    hillL2TraceGradientSpatialCurve_eq_of_sq_eq q _ z (complex_sqrt_sq _)
  simpa only [Function.comp_def,he] using
    (continuous_hillL2TraceGradientSpatialCurve_frequency (SpectralWeight.one.toCoeff q.val))

/-- The coefficient direction is obtained by a bounded Fourier analysis
map applied to the actual physical spatial-gradient curve. -/
theorem hillL2DiscriminantGardnerDirection_eq_unitCurveCoefficients (q : Coeff 2) (E : ℂ) :
    hillL2DiscriminantGardnerDirection q E =
      Coeff.periodDouble (unitCurveCoefficientsCLM (hillL2TraceGradientSpatialCurve q (Complex.sqrt E))) := by
  unfold hillL2DiscriminantGardnerDirection
  congr 1
  symm
  apply unitCurveCoefficients_eq_continuousPeriodOneCoefficients

/-- The actual Gardner tangent is norm-continuous on the entire complex
energy plane, so its closed-contour integrals are genuine L2 tangents. -/
theorem continuous_hillL2DiscriminantGardnerDirection_energy (q : RealPeriodOneHillPotential) :
    Continuous (hillL2DiscriminantGardnerDirection (SpectralWeight.one.toCoeff q.val)) := by
  have hc := Coeff.periodDouble.continuous.comp
    (unitCurveCoefficientsCLM.continuous.comp (continuous_hillL2TraceGradientSpatialCurve_energy q))
  convert hc using 1
  funext E
  exact hillL2DiscriminantGardnerDirection_eq_unitCurveCoefficients _ E

end NLS.KdV
