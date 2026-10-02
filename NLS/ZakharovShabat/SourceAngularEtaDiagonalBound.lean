import NLS.ZakharovShabat.SourcePsiUniformRootNormBound
import NLS.ZakharovShabat.SourcePsiQuotientQuantitativeDisc
import NLS.ZakharovShabat.SourceAngularEndpointBound

/-! # A uniform tail bound for the diagonal eta numerator

On the diagonal the gap numerator is exactly `i` times the deleted
single-root quotient. The bounded-input quotient majorant and the
actual root norm estimate give one bound for all distant indices.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The diagonal numerator has no extra retained-root factor. -/
theorem sourceAngularGapNumerator_diagonal_eq_quotient
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) (z : ℂ) :
    sourceAngularGapNumerator hp hp1 n n s ψ z =
      I*sourceSingleRootQuotientJointProduct hp hp1 n (z,((s n ψ : Coeff p),ψ)) := by
  unfold sourceAngularGapNumerator sourcePsiCandidate sourceSingleRootQuotientJointProduct
    sourceStandardRootOmittedJointProduct
  simp only [div_eq_mul_inv,mul_inv_rev]
  simp only [inv_I]
  ring

namespace SourcePsiSquaredGapComplexExtension
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

theorem exists_local_uniform_diagonal_gapNumerator_tail_bound
    (hs : SourcePsiSquaredGapComplexExtension hp hp1 W s)
    (φ : CoeffPair p) (hφ : φ ∈ W) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧
      ∃ K : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ ψ ∈ U, ∀ n : ℤ, K ≤ n.natAbs →
        ∀ z ∈ closedBall ((Real.pi:ℂ)*n) (Real.pi/8),
          ‖sourceAngularGapNumerator hp hp1 n n s ψ z-I‖ ≤ M := by
  obtain ⟨Vr,hVr,hφr,hVrW,A,hA,hroot⟩ := hs.exists_local_uniform_deletedRoot_norm_bound φ hφ
  obtain ⟨N,ε,_,Vq,hVq,hφq,K,hNK,M,hM,hquot⟩ :=
    exists_local_sourcePsiQuotient_uniformBoundedBallTailMajorant hp hp1 φ hreal A hA.le
  refine ⟨Vr ∩ Vq,hVr.inter hVq,⟨hφr,hφq⟩,inter_subset_left.trans hVrW,K,M,hM,?_⟩
  intro ψ hψ n hn z hz
  obtain ⟨B,hB,hpoint⟩ := hquot ψ hψ.2 (s n ψ : Coeff p) (hroot ψ hψ.1 n)
  have hnN : ¬n.natAbs ≤ N := by omega
  have hzdisc : z ∈ sourceIsolatingDisc hp hp1 φ N ε n := by
    simp only [sourceIsolatingDisc,if_neg hnN]
    exact (mem_closedBall.mp hz).trans_lt (by linarith [Real.pi_pos])
  rw [sourceAngularGapNumerator_diagonal_eq_quotient,
    show I*sourceSingleRootQuotientJointProduct hp hp1 n (z,((s n ψ : Coeff p),ψ))-I =
      I*(sourceSingleRootQuotientJointProduct hp hp1 n (z,((s n ψ : Coeff p),ψ))-1) by ring,
    norm_mul,norm_I,one_mul]
  exact (hpoint n hn z hzdisc).trans
    ((lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' B n).trans hB)

end SourcePsiSquaredGapComplexExtension
end NLS.ZakharovShabat
