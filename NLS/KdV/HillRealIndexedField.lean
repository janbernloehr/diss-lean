import NLS.KdV.HillRealSourceSubmodule
import NLS.KdV.HillIndexedSourceAnalytic
import NLS.KdV.HillRealClosedCurveSources

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The genuine indexed discriminant field on the actual complete real source space. -/
def hillRealIndexedDiscriminantField (n : ℕ) (hn : 1≤n)
    (q : hillRealSourceSubmodule) : hillRealSourceSubmodule :=
  ⟨hillIndexedDiscriminantHamiltonianSource ⟨q.val,q.property⟩ n hn,
    hillEnergyHamiltonianSource_mem_even _ _,
    isReal_hillIndexedDiscriminantHamiltonianSource ⟨q.val,q.property⟩ n hn⟩

theorem hillRealIndexedDiscriminantField_val (n : ℕ) (hn : 1≤n) (q : hillRealSourceSubmodule) :
    (hillRealIndexedDiscriminantField n hn q).val=
      hillIndexedDiscriminantHamiltonianSource ⟨q.val,q.property⟩ n hn := rfl

/-- Actual analytic physical germs make the real indexed spectral field continuously
 differentiable; no regularity assumption on a proposed vector field is supplied. -/
theorem contDiff_hillRealIndexedDiscriminantField (n : ℕ) (hn : 1≤n) :
    ContDiff ℝ 1 (hillRealIndexedDiscriminantField n hn) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  obtain ⟨X,hX,hmatch⟩ := exists_hillIndexedDiscriminantSource_analytic_germ ⟨q.val,q.property⟩ n hn
  let P : hillRealSourceSubmodule →L[ℝ] Coeff 2 :=
    (SpectralWeight.one.toCoeff.restrictScalars ℝ).comp hillRealSourceSubmodule.subtypeL
  have hC : ContDiffAt ℝ 1 (fun p : hillRealSourceSubmodule => X (P p)) q :=
    (hX.contDiffAt.restrict_scalars ℝ).comp q P.contDiff.contDiffAt
  have hF := hillRealSourceProjectionCLM.contDiff.contDiffAt.comp q hC
  have hQ : Continuous (fun p : hillRealSourceSubmodule =>
      (⟨p.val,p.property⟩ : RealPeriodOneHillPotential)) := continuous_subtype_val.subtype_mk _
  have he := hQ.continuousAt.tendsto.eventually hmatch
  apply hF.congr_of_eventuallyEq
  filter_upwards [he] with p hp
  change hillRealIndexedDiscriminantField n hn p=hillRealSourceProjectionCLM (X (SpectralWeight.one.toCoeff p.val))
  rw [hp]
  exact (hillRealSourceProjectionCLM_fixed (hillRealIndexedDiscriminantField n hn p)).symm

end NLS.KdV
