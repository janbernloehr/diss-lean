import NLS.ZakharovShabat.PhysicalHamiltonianDirection

/-! # Analytic physical Hamiltonian vector fields

The literal physical cotangent-to-direction operation is a bounded complex
linear map. The chain rule identifies physical fields under the exact source
Fourier realization, and analytic physical Hamiltonians have analytic fields.
-/

noncomputable section
open Set Metric MeasureTheory Complex Filter Topology NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- Physical Hamiltonian fields commute with the exact Fourier realization. -/
theorem physicalHamiltonianVector_eq_source (H : IntervalPairL2 → ℂ) (u : IntervalPairL2)
    (hH : DifferentiableAt ℂ H u) :
    physicalHamiltonianVector H u = sourcePhysicalL2
      (sourceHamiltonianVector le_rfl (H ∘ sourcePhysicalL2) (sourcePhysicalL2Equiv.symm u)) := by
  have hh : HasFDerivAt H (fderiv ℂ H u)
      (sourcePhysicalL2 (sourcePhysicalL2Equiv.symm u)) := by
    simpa only [sourcePhysicalL2_equiv_symm] using hH.hasFDerivAt
  have hd := hh.comp (sourcePhysicalL2Equiv.symm u)
    (sourcePhysicalL2.hasFDerivAt (x := sourcePhysicalL2Equiv.symm u))
  rw [physicalHamiltonianVector,physicalHamiltonianDirection_eq_source,sourceHamiltonianVector,hd.fderiv]

/-- The physical cotangent-to-direction operation is bounded and complex linear. -/
def physicalHamiltonianDirectionCLM : (IntervalPairL2 →L[ℂ] ℂ) →L[ℂ] IntervalPairL2 :=
  sourcePhysicalL2.comp ((sourceHamiltonianDirection (p := 2) le_rfl).comp
    ((ContinuousLinearMap.compL ℂ (CoeffPair 2) IntervalPairL2 ℂ).flip sourcePhysicalL2))

@[simp] theorem physicalHamiltonianDirectionCLM_apply (L : IntervalPairL2 →L[ℂ] ℂ) :
    physicalHamiltonianDirectionCLM L = physicalHamiltonianDirection L :=
  (physicalHamiltonianDirection_eq_source L).symm

/-- An analytic Hamiltonian has an analytic native physical vector field. -/
theorem analyticOnNhd_physicalHamiltonianVector {U : Set IntervalPairL2}
    {H : IntervalPairL2 → ℂ} (hH : AnalyticOnNhd ℂ H U) :
    AnalyticOnNhd ℂ (physicalHamiltonianVector H) U := by
  intro u hu
  have ha := (physicalHamiltonianDirectionCLM.analyticAt _).comp (hH.fderiv u hu)
  convert! ha using 1
  funext x
  exact (physicalHamiltonianDirectionCLM_apply _).symm

end NLS.ZakharovShabat
