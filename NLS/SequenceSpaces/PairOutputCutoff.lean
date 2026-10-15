import NLS.SequenceSpaces.CompactRowMajorant
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Finite-rank cutoffs followed by bounded reconstruction

The two row majorants control the operator-norm error, including the
norm of the reconstruction map. Every cutoff has finite-dimensional range.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Truncate both output components and apply a bounded reconstruction map. -/
def pairOutputCutoff (T : E →L[ℂ] (Coeff p × Coeff p))
    (Q : (Coeff p × Coeff p) →L[ℂ] F) (S : Finset ℤ) : E →L[ℂ] F :=
  let T₁ := (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)).comp T
  let T₂ := (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)).comp T
  Q.comp (((truncateCLM S).comp T₁).prod ((truncateCLM S).comp T₂))

/-- The finite cutoff is the sum of the reconstructed coordinate vectors. -/
theorem pairOutputCutoff_apply (T : E →L[ℂ] (Coeff p × Coeff p))
    (Q : (Coeff p × Coeff p) →L[ℂ] F) (S : Finset ℤ) (h : E) :
    pairOutputCutoff T Q S h =
      ∑ n ∈ S, Q (lp.single p n ((T h).1 n),lp.single p n ((T h).2 n)) := by
  change Q (truncate S (T h).1,truncate S (T h).2) = _
  rw [← map_sum]
  congr 1
  apply Prod.ext
  · exact (map_sum (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p))
      (fun n => (lp.single p n ((T h).1 n),lp.single p n ((T h).2 n))) S).symm
  · exact (map_sum (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p))
      (fun n => (lp.single p n ((T h).1 n),lp.single p n ((T h).2 n))) S).symm

theorem norm_pairOutputCutoff_sub_le
    (T : E →L[ℂ] (Coeff p × Coeff p))
    (Q : (Coeff p × Coeff p) →L[ℂ] F)
    (b₁ b₂ : Coeff p)
    (hrow : ∀ (n : ℤ) (h : E),
      ‖(T h).1 n‖ ≤ ‖b₁ n‖*‖h‖ ∧ ‖(T h).2 n‖ ≤ ‖b₂ n‖*‖h‖)
    (S : Finset ℤ) :
    ‖pairOutputCutoff T Q S - Q.comp T‖ ≤
      ‖Q‖ * max ‖Coeff.truncate S b₁-b₁‖ ‖Coeff.truncate S b₂-b₂‖ := by
  let T₁ := (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p)).comp T
  let T₂ := (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p)).comp T
  have h₁ : ‖(Coeff.truncateCLM S).comp T₁-T₁‖ ≤ ‖Coeff.truncate S b₁-b₁‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    exact Coeff.norm_truncate_operator_sub_le_rowTail T₁ b₁ (fun n h => (hrow n h).1) S
  have h₂ : ‖(Coeff.truncateCLM S).comp T₂-T₂‖ ≤ ‖Coeff.truncate S b₂-b₂‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    exact Coeff.norm_truncate_operator_sub_le_rowTail T₂ b₂ (fun n h => (hrow n h).2) S
  have he : Q.comp (((Coeff.truncateCLM S).comp T₁).prod ((Coeff.truncateCLM S).comp T₂)) - Q.comp T =
      Q.comp (((Coeff.truncateCLM S).comp T₁-T₁).prod ((Coeff.truncateCLM S).comp T₂-T₂)) := by
    ext h : 1
    change Q (Coeff.truncate S (T₁ h), Coeff.truncate S (T₂ h))-Q (T₁ h,T₂ h) =
      Q (Coeff.truncate S (T₁ h)-T₁ h, Coeff.truncate S (T₂ h)-T₂ h)
    rw [← map_sub]
    rfl
  change ‖Q.comp (((Coeff.truncateCLM S).comp T₁).prod ((Coeff.truncateCLM S).comp T₂)) - Q.comp T‖ ≤ _
  rw [he]
  refine (Q.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg Q))
  rw [ContinuousLinearMap.opNorm_prod, Prod.norm_def]
  exact max_le_max h₁ h₂

theorem finiteDimensional_range_pairOutputCutoff
    (T : E →L[ℂ] (Coeff p × Coeff p))
    (Q : (Coeff p × Coeff p) →L[ℂ] F) (S : Finset ℤ) :
    FiniteDimensional ℂ (LinearMap.range
      (pairOutputCutoff T Q S).toLinearMap) := by
  classical
  let e₁ (n : ℤ) := Q (lp.single p n 1, 0)
  let e₂ (n : ℤ) := Q (0, lp.single p n 1)
  let U := Submodule.span ℂ (e₁ '' (S : Set ℤ) ∪ e₂ '' (S : Set ℤ))
  let : FiniteDimensional ℂ U := FiniteDimensional.span_of_finite ℂ
    ((S.finite_toSet.image e₁).union (S.finite_toSet.image e₂))
  apply Submodule.finiteDimensional_of_le (S₂ := U)
  rintro _ ⟨h, rfl⟩
  change Q (Coeff.truncate S (T h).1, Coeff.truncate S (T h).2) ∈ U
  have he : (Coeff.truncate S (T h).1, Coeff.truncate S (T h).2) =
      ∑ n ∈ S, (lp.single p n ((T h).1 n), lp.single p n ((T h).2 n)) := by
    apply Prod.ext
    · exact (map_sum (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p))
        (fun n => (lp.single p n ((T h).1 n), lp.single p n ((T h).2 n))) S).symm
    · exact (map_sum (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p))
        (fun n => (lp.single p n ((T h).1 n), lp.single p n ((T h).2 n))) S).symm
  rw [he, map_sum]
  apply Submodule.sum_mem
  intro n hn
  have hx : Q (lp.single p n ((T h).1 n), lp.single p n ((T h).2 n)) =
      (T h).1 n • e₁ n + (T h).2 n • e₂ n := by
    dsimp only [e₁, e₂]
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    apply Prod.ext <;> simp [← lp.single_smul]
  rw [hx]
  apply U.add_mem
  · exact U.smul_mem _ (Submodule.subset_span (Or.inl ⟨n,hn,rfl⟩))
  · exact U.smul_mem _ (Submodule.subset_span (Or.inr ⟨n,hn,rfl⟩))

end NLS.Coeff
