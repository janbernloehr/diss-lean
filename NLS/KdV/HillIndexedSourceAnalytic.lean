import NLS.KdV.HillEnergyGradientAnalytic
import NLS.KdV.HillCurveRealizationCLM
import NLS.KdV.HillIndexedDiscriminantSources
import NLS.KdV.HillDirichletAnalyticLabels

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The genuine fixed-energy discriminant Hamiltonian source is entire jointly in
energy and the rough potential, in the original weighted coefficient norm. -/
theorem analyticOnNhd_hillEnergyHamiltonianSource_joint :
    AnalyticOnNhd ℂ (fun p : ℂ × Coeff 2 => hillEnergyHamiltonianSource p.2 p.1) univ := by
  intro p _
  have hG := (analyticOnNhd_hillEnergyDiscriminantGradientSpatialCurve_joint p (mem_univ _)).neg
  have hF := (hillCurveRealizationCLM.analyticAt _).comp hG
  apply hF.congr
  exact Eventually.of_forall (fun r => hillCurveRealizationCLM_closed _ _)

/-- Each actual indexed discriminant source has a Banach-analytic physical germ,
including at zero terminal sheets and collapsed gaps. -/
theorem exists_hillIndexedDiscriminantSource_analytic_germ
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    ∃ X : Coeff 2 → WeightedCoeff SpectralWeight.one.toWeight 2,
      AnalyticAt ℂ X (SpectralWeight.one.toCoeff q.val) ∧
      ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
        X (SpectralWeight.one.toCoeff p.val)=hillIndexedDiscriminantHamiltonianSource p n hn := by
  obtain ⟨a,ha,_,_,hmatch⟩ := exists_hillDirichletEnergy_analytic_extension q n hn
  refine ⟨fun p => hillEnergyHamiltonianSource p (a p),?_,?_⟩
  · exact (analyticOnNhd_hillEnergyHamiltonianSource_joint
      (a (SpectralWeight.one.toCoeff q.val),SpectralWeight.one.toCoeff q.val) (mem_univ _)).comp
      (f := fun p : Coeff 2 => (a p,p)) (ha.prod analyticAt_id)
  · filter_upwards [hmatch] with p hp
    change hillEnergyHamiltonianSource (SpectralWeight.one.toCoeff p.val)
      (a (SpectralWeight.one.toCoeff p.val))=hillEnergyHamiltonianSource
        (SpectralWeight.one.toCoeff p.val) (hillDirichletEnergy p.val p.property.1 p.property.2 n hn)
    exact congrArg (hillEnergyHamiltonianSource (SpectralWeight.one.toCoeff p.val)) hp

end NLS.KdV
