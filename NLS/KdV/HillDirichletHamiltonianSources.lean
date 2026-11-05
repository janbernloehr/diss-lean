import NLS.KdV.HillClosedCurveDirections
import NLS.KdV.HillDirichletDarbouxCotangents
import NLS.KdV.HillDirichletQuadraticSystem

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The negative spatial Dirichlet gradient, as an actual period-one coefficient source. -/
def hillDirichletHamiltonianSource (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    WeightedCoeff SpectralWeight.one.toWeight 2 :=
  hillClosedCurveCoefficients (-(hillDirichletGradientSpatialCurve q n hn)) (by
    simp only [ContinuousMap.neg_apply,(hillDirichletGradientSpatialCurve_endpoints q n hn).1,
      (hillDirichletGradientSpatialCurve_endpoints q n hn).2])

theorem hillDirichletHamiltonianSource_mem_even (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    SpectralWeight.one.toCoeff (hillDirichletHamiltonianSource q n hn)∈Coeff.paritySubspace 0 :=
  hillClosedCurveCoefficients_mem_even _ _

/-- Pairing the source with an arbitrary actual physical cotangent. -/
theorem hillDirichletHamiltonianSource_pairing (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n)
    (v : Curve ℂ) :
    hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff (hillDirichletHamiltonianSource q n hn)) v=
      -unitComplexCurvePairing (hillDirichletGradientSpatialCurve q n hn) v := by
  rw [hillDirichletHamiltonianSource,hillClosedCurveCoefficients_pairing]
  exact map_neg (unitComplexCurvePairing.flip v) _

/-- The actual log-norming branch varies by the nonzero diagonal Darboux constant. -/
theorem hillDirichletLogBranch_dirichletHamiltonianSource_fderiv
    (q : RealPeriodOneHillPotential) (n k : ℕ) (hn : 1≤n) (hk : 1≤k)
    (a : Coeff 2 → ℂ) (ha : AnalyticAt ℂ a (SpectralWeight.one.toCoeff q.val))
    (ha0 : a (SpectralWeight.one.toCoeff q.val)=(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ))
    (hz : ∀ᶠ p in 𝓝 (SpectralWeight.one.toCoeff q.val),hillL2DirichletCharacteristic p (a p)=0) :
    (fderiv ℂ (fun p : Coeff 2 => Complex.log ((-1 : ℂ)^n*hillL2DirichletSlope p (a p)))
      (SpectralWeight.one.toCoeff q.val))
      (SpectralWeight.one.toCoeff (hillDirichletHamiltonianSource q k hk))=
        -(if n=k then (1/2 : ℂ) else 0) := by
  rw [hillLogNormingGradient_represents_branch q n hn a ha ha0 hz]
  rw [←hillPhysicalDirectionPairing_apply]
  rw [hillDirichletHamiltonianSource_pairing]
  congr 1
  calc
    _ = ∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn) x*
        deriv (NLS.LinearVolterra.extend (hillDirichletGradientCurve q k hk)) x := by
      rw [unitComplexCurvePairing_apply]
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
      filter_upwards [ae_hasDerivAt_hillDirichletGradientCurve q k hk] with x hx
      change NLS.LinearVolterra.extend (hillDirichletGradientSpatialCurve q k hk) x*
        NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn) x=
          NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn) x*
            deriv (NLS.LinearVolterra.extend (hillDirichletGradientCurve q k hk)) x
      rw [hx.deriv,mul_comm]
    _ = _ := hillLogDirichletGardnerBracket_eq q n k hn hk

end NLS.KdV
