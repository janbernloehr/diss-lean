import NLS.KdV.HillDiscriminantDirichletBrackets
import NLS.KdV.HillPhysicalActionGradients

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis Metric
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



theorem unitComplexCurvePairing_energy_dirichlet
    (q : RealPeriodOneHillPotential) (energy : ℂ) (n : ℕ) (hn : 1≤n) :
    unitComplexCurvePairing (hillEnergyDiscriminantGradientCurve (SpectralWeight.one.toCoeff q.val) energy)
      (hillDirichletGradientSpatialCurve q n hn)=
      hillDiscriminantDirichletGardnerBracket q (Complex.sqrt energy) n hn := by
  symm
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
  filter_upwards [ae_hasDerivAt_hillDirichletGradientCurve q n hn] with x hx
  rw [hx.deriv]
  rfl

theorem hillEnergyGradientContour_dirichlet_bracket
    (q : RealPeriodOneHillPotential) (a : ℂ → ℂ) (c : ℝ) (r : ℝ) (hr : 0<r)
    (ha : ContinuousOn a (sphere (c : ℂ) r)) (n : ℕ) (hn : 1≤n) :
    (∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend
      (hillEnergyGradientContour (SpectralWeight.one.toCoeff q.val) a c r) x*
        deriv (NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn)) x)=
      ∮ z in C((c : ℂ),r),a z*
        ((hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) z*
          ((hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val)
            (hillDirichletEnergy q.val q.property.1 q.property.2 n hn))^2-1))/
        (2*(scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)*
          (z-(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)))) := by
  calc
    _ = unitComplexCurvePairing
        (hillEnergyGradientContour (SpectralWeight.one.toCoeff q.val) a c r)
        (hillDirichletGradientSpatialCurve q n hn) := by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
      filter_upwards [ae_hasDerivAt_hillDirichletGradientCurve q n hn] with x hx
      rw [hx.deriv]
      rfl
    _ = ∮ z in C((c : ℂ),r),a z*
        hillDiscriminantDirichletGardnerBracket q (Complex.sqrt z) n hn := by
      change (unitComplexCurvePairing.flip (hillDirichletGradientSpatialCurve q n hn))
        (hillEnergyGradientContour (SpectralWeight.one.toCoeff q.val) a c r)=_
      rw [hillEnergyGradientContour,
        map_circleIntegral (unitComplexCurvePairing.flip (hillDirichletGradientSpatialCurve q n hn))
          (circleIntegrable_hillEnergyGradientContour_integrand
            (SpectralWeight.one.toCoeff q.val) a c r hr.le ha)]
      simp only [map_smul,ContinuousLinearMap.flip_apply,smul_eq_mul,
        unitComplexCurvePairing_energy_dirichlet]
    _ = _ := by
      apply circleIntegral_eq_of_eq_on_nonreal _ _ c r hr
      intro z _ hz
      have hne : (Complex.sqrt z)^2≠(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ) := by
        rw [complex_sqrt_sq]
        intro he
        exact hz (by rw [he];exact ofReal_im _)
      rw [hillDiscriminantDirichletGardnerBracket_eq q (Complex.sqrt z) n hn hne,complex_sqrt_sq]
      rfl

/-- Every actual physical moment flow has the original Dirichlet motion
given by this exact spectral Cauchy contour, at all gap indices and orders.
Real-axis crossings are handled by finite-exception circle comparison. -/
theorem hillPhysicalMomentGradient_dirichlet_bracket
    (q : RealPeriodOneHillPotential) (k n : ℕ) (hk : 1≤k) (hn : 1≤n) (m : ℕ) :
    (∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend
      (hillPhysicalMomentGradient q.val q.property.1 q.property.2 k m) x*
        deriv (NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn)) x)=
      ∮ z in C((hillRealGapCenter q.val q.property.1 q.property.2 k : ℂ),
        hillRealGapHalfLength q.val q.property.1 q.property.2 k+hillRealGapCollar q.val q.property.1 q.property.2 k),
        hillPhysicalMomentGradientWeight (SpectralWeight.one.toCoeff q.val) m z*
        ((hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q.val) z*
          ((hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val)
            (hillDirichletEnergy q.val q.property.1 q.property.2 n hn))^2-1))/
        (2*(scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)*
          (z-(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)))) :=
  hillEnergyGradientContour_dirichlet_bracket q
    (hillPhysicalMomentGradientWeight (SpectralWeight.one.toCoeff q.val) m)
    (hillRealGapCenter q.val q.property.1 q.property.2 k)
    (hillRealGapHalfLength q.val q.property.1 q.property.2 k+hillRealGapCollar q.val q.property.1 q.property.2 k)
    (add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q.val q.property.1 q.property.2 k hk).1
      (hillRealGapContour_geometry q.val q.property.1 q.property.2 k hk).2.1)
    (continuousOn_hillPhysicalMomentGradientWeight q.val q.property.1 q.property.2 k hk m) n hn

end NLS.KdV
