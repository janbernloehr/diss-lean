import NLS.KdV.HillHamiltonianSourceContinuity
import NLS.KdV.HillEnergyDiscriminantGradients

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The actual negative spatial energy-discriminant cotangent, realized in the
original weighted period-one Hill source space. -/
def hillEnergyHamiltonianSource (p : Coeff 2) (E : ℂ) : WeightedCoeff SpectralWeight.one.toWeight 2 :=
  hillClosedCurveCoefficients (-(hillEnergyDiscriminantGradientSpatialCurve p E))
    (congrArg Neg.neg ((hillDiscriminantGradientSpatialCurve_endpoints p (Complex.sqrt E)).1.trans
      (hillDiscriminantGradientSpatialCurve_endpoints p (Complex.sqrt E)).2.symm))

theorem hillEnergyHamiltonianSource_mem_even (p : Coeff 2) (E : ℂ) :
    SpectralWeight.one.toCoeff (hillEnergyHamiltonianSource p E)∈Coeff.paritySubspace 0 :=
  hillClosedCurveCoefficients_mem_even _ _

theorem hillEnergyHamiltonianSource_pairing (p : Coeff 2) (E : ℂ) (v : Curve ℂ) :
    hillPhysicalDirectionPairing (SpectralWeight.one.toCoeff (hillEnergyHamiltonianSource p E)) v=
      -unitComplexCurvePairing (hillEnergyDiscriminantGradientSpatialCurve p E) v := by
  rw [hillEnergyHamiltonianSource,hillClosedCurveCoefficients_pairing]
  exact map_neg (unitComplexCurvePairing.flip v) _

/-- These actual coefficient directions are isospectral at every fixed energy. -/
theorem hillEnergyHamiltonianSource_isospectral (p : Coeff 2) (E energy : ℂ) :
    (fderiv ℂ (fun q : Coeff 2 => hillL2Discriminant q energy) p)
      (SpectralWeight.one.toCoeff (hillEnergyHamiltonianSource p E))=0 := by
  rw [hillEnergyDiscriminantGradient_represents_potential,hillEnergyHamiltonianSource_pairing]
  have hc : unitComplexCurvePairing (hillEnergyDiscriminantGradientSpatialCurve p E)
      (hillEnergyDiscriminantGradientCurve p energy)=
      unitComplexCurvePairing (hillEnergyDiscriminantGradientCurve p energy)
        (hillEnergyDiscriminantGradientSpatialCurve p E) := by
    rw [unitComplexCurvePairing_apply,unitComplexCurvePairing_apply,mul_comm]
  rw [hc]
  have hz : unitComplexCurvePairing (hillEnergyDiscriminantGradientCurve p energy)
      (hillEnergyDiscriminantGradientSpatialCurve p E)=0 := by
    rw [unitComplexCurvePairing_apply]
    exact (hillDiscriminantGardnerBracket_eq_curveIntegral p (Complex.sqrt energy) (Complex.sqrt E)).symm.trans
      (hillDiscriminantGardnerBracket_eq_zero p (Complex.sqrt energy) (Complex.sqrt E))
  rw [hz,neg_zero]

/-- Every discriminant Hamiltonian source has zero mean. -/
theorem hillEnergyHamiltonianSource_mean_zero (p : Coeff 2) (E : ℂ) :
    (hillEnergyHamiltonianSource p E).val 0=0 := by
  rw [hillEnergyHamiltonianSource,hillClosedCurveCoefficients_zero]
  change (∫ x in (0 : ℝ)..1,-NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientSpatialCurve p E) x)=0
  rw [intervalIntegral.integral_neg]
  apply neg_eq_zero.mpr
  have hd := ae_hasDerivAt_hillEnergyDiscriminantGradientCurve p E
  rw [restrict_Ioc_eq_restrict_Icc] at hd
  have he := (ae_restrict_iff' measurableSet_Icc).mp hd
  have hh := integral_eq_sub_of_ac_of_ae_hasDerivAt (hillEnergyDiscriminantGradient_H1 p E).1
    ((continuous_extend (hillEnergyDiscriminantGradientSpatialCurve p E)).intervalIntegrable 0 1)
    (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using he)
  rw [hh]
  dsimp only [NLS.LinearVolterra.extend]
  rw [projIcc_of_mem _ (show (1 : ℝ)∈Icc 0 1 by norm_num),
    projIcc_of_mem _ (show (0 : ℝ)∈Icc 0 1 by norm_num),
    hillEnergyDiscriminantGradientCurve,
    (hillDiscriminantGradientCurve_endpoints p (Complex.sqrt E)).1,
    (hillDiscriminantGradientCurve_endpoints p (Complex.sqrt E)).2,sub_self]

/-- The actual energy-discriminant Hamiltonian source varies jointly continuously. -/
theorem continuous_hillEnergyHamiltonianSource_joint :
    Continuous (fun t : ℂ × Coeff 2 => hillEnergyHamiltonianSource t.2 t.1) := by
  apply continuous_hillClosedCurveCoefficients_family
  exact continuous_hillEnergyDiscriminantGradientSpatialCurve_joint.neg

/-- The fixed-energy discriminant source evaluated at its own actual moving Dirichlet label. -/
def hillIndexedDiscriminantHamiltonianSource (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    WeightedCoeff SpectralWeight.one.toWeight 2 :=
  hillEnergyHamiltonianSource (SpectralWeight.one.toCoeff q.val)
    (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)

theorem hillIndexedDiscriminantHamiltonianSource_isospectral
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (energy : ℂ) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p energy) (SpectralWeight.one.toCoeff q.val))
      (SpectralWeight.one.toCoeff (hillIndexedDiscriminantHamiltonianSource q n hn))=0 :=
  hillEnergyHamiltonianSource_isospectral _ _ _

theorem continuous_hillIndexedDiscriminantHamiltonianSource (n : ℕ) (hn : 1≤n) :
    Continuous (fun q : RealPeriodOneHillPotential => hillIndexedDiscriminantHamiltonianSource q n hn) :=
  Continuous.comp (f := fun q : RealPeriodOneHillPotential =>
      ((hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ),SpectralWeight.one.toCoeff q.val))
    continuous_hillEnergyHamiltonianSource_joint
    ((Complex.continuous_ofReal.comp (continuous_hillDirichletEnergy n hn)).prodMk
      (SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val))

end NLS.KdV
