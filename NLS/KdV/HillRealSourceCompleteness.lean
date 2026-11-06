import NLS.KdV.HillLabelContinuity
import NLS.SequenceSpaces.WeightedFiniteCoefficients
import Mathlib.Topology.Baire.CompleteMetrizable

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



private theorem closed_conjugate_constraints {E : Type} [TopologicalSpace E]
    (f : E → ℤ → ℂ) (hf : ∀ k, Continuous (fun q => f q k)) :
    IsClosed {q | ∀ k : ℤ, f q (-k)=conj (f q k)} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun k => isClosed_eq (hf (-k)) (Complex.continuous_conj.comp (hf k)))

private theorem closed_real_coeff : IsClosed {p : Coeff 2 | IsRealHillPotential p} :=
  closed_conjugate_constraints (fun p : Coeff 2 => p)
    (fun k => (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).continuous)

private theorem complete_closed_source {E : Type} [MetricSpace E] [CompleteSpace E]
    (S : Set E) (hS : IsClosed S) : CompleteSpace S :=
  hS.isComplete.completeSpace_coe

/-- The actual real period-one Hill domain is closed in the original weighted Hilbert space. -/
theorem isClosed_realPeriodOneHillPotential :
    IsClosed {q : WeightedCoeff SpectralWeight.one.toWeight 2 |
      SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0 ∧
        IsRealHillPotential (SpectralWeight.one.toCoeff q)} :=
  ((Coeff.isClosed_paritySubspace (p := 2) 0).inter closed_real_coeff).preimage
    SpectralWeight.one.toCoeff.continuous

/-- The real physical source space is complete in its inherited L2 metric. -/
theorem completeSpace_realPeriodOneHillPotential : CompleteSpace RealPeriodOneHillPotential :=
  complete_closed_source _ isClosed_realPeriodOneHillPotential

end NLS.KdV
