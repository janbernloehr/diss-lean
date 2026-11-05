import NLS.KdV.HillHminusActionCotangent
import NLS.KdV.HillClosedCurveSourceCoefficients
import NLS.KdV.HillContourHamiltonianSources
import NLS.Poisson.GardnerHamiltonianDirection

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.KdV

/-- The genuine Gardner Hamiltonian vector of the ORIGINAL action is the
NEGATIVE of the previously constructed physical contour source. The sign
is fixed coefficientwise with the actual unit-period 2*pi multiplier. -/
theorem hillOriginalAction_hminus_HamiltonianVector_eq_neg_source
    (q : RealPeriodOneHillPotential) (n : ℕ+)
    (F : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) =
        (hillRealGapIntegral p.val p.property.1 p.property.2 n 0 : ℂ)) :
    NLS.Poisson.gardnerHamiltonianVector F (hillOriginalHminusSource q.val) =
      -hillOriginalHminusSource
        (hillPhysicalMomentHamiltonianSource q.val q.property.1 q.property.2 n n.pos 0) := by
  let a := hillPhysicalMomentGradientWeight (SpectralWeight.one.toCoeff q.val) 0
  let c : ℂ := hillRealGapCenter q.val q.property.1 q.property.2 n
  let R := hillRealGapHalfLength q.val q.property.1 q.property.2 n +
    hillRealGapCollar q.val q.property.1 q.property.2 n
  have hR : 0 ≤ R := add_nonneg
    (hillRealGapContour_geometry q.val q.property.1 q.property.2 n n.pos).1
    (hillRealGapContour_geometry q.val q.property.1 q.property.2 n n.pos).2.1.le
  have ha : ContinuousOn a (sphere c R) :=
    continuousOn_hillPhysicalMomentGradientWeight q.val q.property.1 q.property.2 n n.pos 0
  let f := hillEnergyGradientContour (SpectralWeight.one.toCoeff q.val) a c R
  let g := hillEnergyGradientSpatialContour (SpectralWeight.one.toCoeff q.val) a c R
  have hp : NLS.LinearVolterra.extend f 1 = NLS.LinearVolterra.extend f 0 := by
    dsimp only [NLS.LinearVolterra.extend]
    rw [projIcc_of_mem _ (show (1:ℝ) ∈ Icc 0 1 by norm_num),
      projIcc_of_mem _ (show (0:ℝ) ∈ Icc 0 1 by norm_num)]
    exact (hillEnergyGradientContours_closed _ a c R hR ha).1.symm
  have hd := Fourier.unitFourierCoefficient_ac_periodic_prescribed_derivative
    (NLS.LinearVolterra.extend f) (NLS.LinearVolterra.extend g)
    (hillEnergyGradientContour_H1 _ a c R hR ha).1 (continuous_extend g)
    (ae_hasDerivAt_hillEnergyGradientContour _ a c R hR ha) hp
  apply Subtype.ext
  funext k
  change (NLS.Poisson.gardnerHamiltonianVector F (hillOriginalHminusSource q.val)).val k =
    -(hillOriginalHminusSource
      (hillPhysicalMomentHamiltonianSource q.val q.property.1 q.property.2 n n.pos 0)).val k
  rw [NLS.Poisson.gardnerHamiltonianVector_apply,
    hillOriginalAction_hminus_gradient_coefficients q n F hF hmatch]
  change (2 * Real.pi : ℂ) * I * k * Fourier.unitFourierCoefficient (NLS.LinearVolterra.extend f) k = _
  calc
    _ = Fourier.unitFourierCoefficient (NLS.LinearVolterra.extend g) k := by
      rw [hd k]
      ring
    _ = _ := by
      change _ = -(hillOriginalHminusSource
        (hillClosedCurveCoefficients (-g)
          (congrArg Neg.neg (hillEnergyGradientContours_closed _ a c R hR ha).2))).val k
      rw [hillOriginalHminusSource_closedCurve_apply]
      simp only [Fourier.unitFourierCoefficient,NLS.LinearVolterra.extend,
        ContinuousMap.neg_apply,neg_mul,intervalIntegral.integral_neg,neg_neg]

end NLS.KdV
