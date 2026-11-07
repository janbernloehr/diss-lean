import NLS.Articles.MKdVNLSHierarchies.FullFundamentalSymmetries
import NLS.ZakharovShabat.AppendixPhaseConventionCounterexample

/-! # Explicit reconciliation of the paper's two displayed operator orders

Section2 and the printed Lemma13 phase formula use the upper phi1 convention.
The local page5/Appendix displays instead put phi2 in that position. Their
actual operator is the Section2 operator at P*phi, with spectral reflection
and signed-index reversal. A real-type counterexample rules out combining
the Appendix local operator literally with its printed positive phase gauge.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.Articles.MKdVNLSHierarchies

theorem appendix_operator_source_adapter (φ : CoeffPair 2) (f : ℝ → ℂ × ℂ) (x : ℝ) :
    appendixDisplayedOperator (physicalBase (periodOnePotential φ)) f x =
      physicalOperator (physicalBase (periodOnePotential (sourceComponentSwap φ))) f x :=
  appendixDisplayedOperator_source_adapter φ f x

theorem appendix_fundamental_spectral_adapter (φ : CoeffPair 2) (z : ℂ) (x : ℝ) :
    appendixFundamentalMatrix φ z x =
      componentSwapMatrix (l2WholeLineFundamentalMatrix (sourcePhysicalL2 φ) (-z) x) :=
  appendixFundamentalMatrix_adapter φ z x

theorem appendix_signed_label_adapter {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (n : ℤ) :
    appendixPeriodicLeft hp hp1 φ n =
        -canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) (-n) ∧
    appendixPeriodicRight hp hp1 φ n =
        -canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) (-n) :=
  appendix_signed_endpoint_adapter hp hp1 φ n

/-- Retaining the literal Appendix local operator reverses the phase gauge;
P and pure T keep their printed matrix form. All real times and original
complex H0 sources, hence the original real-type domain, are included. -/
theorem lemma13_literal_appendix_corrected (φ : CoeffPair 2) (α : ℝ) (z : ℂ) (x : ℝ) :
    appendixFundamentalMatrix (sourceComponentSwap φ) (-z) x =
        componentSwapMatrix (appendixFundamentalMatrix φ z x) ∧
    appendixFundamentalMatrix (sourceMidpointReflection φ) (-z) x =
        !![-1,0;0,1]*appendixFundamentalMatrix φ z (1-x)*(appendixMonodromy φ z)⁻¹*!![-1,0;0,1] ∧
    appendixFundamentalMatrix (sourcePhaseRotation α φ) z x =
        reciprocalScalingMatrix ((exp ((α:ℂ)*I))⁻¹) (appendixFundamentalMatrix φ z x) :=
  ⟨appendixFundamentalMatrix_componentSwap φ z x,
   appendixFundamentalMatrix_midpointReflection φ z x,appendixFundamentalMatrix_phase φ α z x⟩

theorem lemma13_literal_appendix_phase_false :
    ∃ φ : CoeffPair 2, φ ∈ realTypeSourceSubmodule 2 ∧
      appendixFundamentalMatrix (sourcePhaseRotation (Real.pi/2) φ) 0 1 ≠
        reciprocalScalingMatrix (exp ((((Real.pi/2:ℝ):ℂ))*I)) (appendixFundamentalMatrix φ 0 1) :=
  ⟨appendixRealConstantWitness,appendixRealConstantWitness_realType,appendix_printed_phase_formula_false⟩

end NLS.Articles.MKdVNLSHierarchies
