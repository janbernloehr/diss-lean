import NLS.ZakharovShabat.SourcePsiOriginalComplexInverseBounds

/-!
# The inverse-bound step of Lemma 12.10 on the original domain

The unchanged open connected source domain retains Proposition 12.9.
At every point of each original real Omega, Q* is invertible and one
joint complex radius and inverse norm bound work on all deleted spaces.
Construction of the common analytic solution extension is a later step.
-/

noncomputable section
open Set Complex Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original-domain inverse bounds, without shrinking the preceding W. -/
theorem sourceLemma12_10_inverseBounds (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceProposition12_9Data hp hp1 W ∧
      ∀ {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ},
        SourceIsolatingNeighborhoods hp hp1 V D c → IsOpen V →
        ∀ t : realTypeSourceSubmodule p × RealCoeff p, t ∈ sourcePsiOriginalOmega V D →
          Function.Bijective (sourcePsiOriginalLimitOperator hp hp1 (RealCoeff.complexCLM p t.2) t.1) ∧
          ∃ δ M : ℝ, 0 < δ ∧ 0 ≤ M ∧ ∀ n : ℤ,
            ∀ u ∈ ball (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p t.2),(t.1:CoeffPair p)) δ,
              ∃ R : DeletedCoeff p n →L[ℂ] DeletedCoeff p n,
                (sourcePsiOriginalRootJacobian hp hp1 n u.1 u.2).comp R = ContinuousLinearMap.id ℂ (DeletedCoeff p n) ∧
                R.comp (sourcePsiOriginalRootJacobian hp hp1 n u.1 u.2) = ContinuousLinearMap.id ℂ (DeletedCoeff p n) ∧
                ‖R‖ ≤ M := by
  obtain ⟨W,ho,hc,hr,H⟩ := sourceProposition12_9 hp hp1
  refine ⟨W,ho,hc,hr,H,?_⟩
  intro V D c hD hV t ht
  have htW := hr t.1.property
  exact ⟨H.previous.previous.previous.previous.previous.originalLimitOperator_bijective
    ho hD hV t.1 htW ht.1 t.1.property (RealCoeff.complexCLM p t.2) ht.2 (fun k => by simp),
    H.originalRootJacobian_local_inverse_bound_complex ho hD hV t htW ht⟩

end NLS.ZakharovShabat
