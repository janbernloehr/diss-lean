import NLS.ZakharovShabat.SourceIndexedHigherActionWeighted
import NLS.ZakharovShabat.SourceHigherSobolevHigherActionBound
import NLS.SequenceSpaces.LocallyBoundedRealization

/-! # Analytic original higher-action sequences on the full Sobolev domain

Absolute convergence and Banach analyticity hold on the entire preimage of
the retained Section 19 domain, simultaneously through printed level 2s+1.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ZakharovShabat

/-- The original higher-action sequence, with its exact coordinates on the proved domain. -/
def sourceIndexedHigherSobolevActionSequence (s k : ℕ) (a : SobolevSource s) : Coeff 1 :=
  Coeff.ofFunctionOrZero 1 (fun n => sourceIndexedHigherAction (by simp) (by norm_num) n k (higherSobolevSourceInclusion s a))

namespace SourceSection19Data
variable {W U : Set (CoeffPair 2)} (Q : SourceSection19Data (by simp) (by norm_num) W U)
include Q

theorem exists_local_higherSobolev_indexedAction_bound
    (s : ℕ) (a : SobolevSource s) (ha : higherSobolevSourceInclusion s a ∈ U) :
    ∃ V : Set (SobolevSource s), IsOpen V ∧ a ∈ V ∧
      ∃ C : ℝ, ∀ b ∈ V, ∀ k : ℕ, k ≤ 2*s → ∃ J : Coeff 1,
        (∀ n : ℤ, J n = sourceIndexedHigherAction (by simp) (by norm_num) n k
          (higherSobolevSourceInclusion s b)) ∧ ‖J‖ ≤ C :=
  Q.exists_local_weightedIndexedHigherAction_bound
    (SpectralWeight.sobolev (s : ℝ) (Nat.cast_nonneg s))
    (higherSobolevSourceInclusion s) (higherSobolevSourceWeightedPeriodOne s)
    (weightedBaseToPair_higherSobolevSourceWeightedPeriodOne s) (2*s)
    (higherAction_higherSobolev_weight_bound s) a ha

theorem indexedHigherSobolevActionSequence_apply (s k : ℕ) (hk : k ≤ 2*s)
    (a : SobolevSource s) (ha : higherSobolevSourceInclusion s a ∈ U) (n : ℤ) :
    sourceIndexedHigherSobolevActionSequence s k a n =
      sourceIndexedHigherAction (by simp) (by norm_num) n k (higherSobolevSourceInclusion s a) := by
  obtain ⟨V,_,haV,_,hb⟩ := Q.exists_local_higherSobolev_indexedAction_bound s a ha
  obtain ⟨g,hg,_⟩ := hb a haV k hk
  rw [sourceIndexedHigherSobolevActionSequence,Coeff.ofFunctionOrZero_eq_of_coordinates _ g hg]
  exact hg n

theorem analytic_indexedHigherSobolevActionSequence (s k : ℕ) (hk : k ≤ 2*s) :
    AnalyticOnNhd ℂ (sourceIndexedHigherSobolevActionSequence s k)
      (higherSobolevSourceInclusion s ⁻¹' U) := by
  let L := higherSobolevSourceInclusion s
  intro a ha
  obtain ⟨V,hV,haV,C,hbound⟩ := Q.exists_local_higherSobolev_indexedAction_bound s a ha
  let T := V ∩ L ⁻¹' U
  have hT : IsOpen T := hV.inter (Q.source_open.preimage L.continuous)
  have hA : AnalyticOnNhd ℂ (sourceIndexedHigherSobolevActionSequence s k) T := by
    apply Coeff.analyticOnNhd_of_bounded_coordinatewise _ hT ?_ C ?_
    · intro n b hb
      have h := (Q.analytic_indexedHigherAction n k (L b) hb.2).comp (L.analyticAt b)
      apply h.congr
      filter_upwards [hT.mem_nhds hb] with c hc
      exact (Q.indexedHigherSobolevActionSequence_apply s k hk c hc.2 n).symm
    · intro b hb
      obtain ⟨g,hg,hgn⟩ := hbound b hb.1 k hk
      rwa [sourceIndexedHigherSobolevActionSequence,Coeff.ofFunctionOrZero_eq_of_coordinates _ g hg]
  exact hA a ⟨haV,ha⟩

theorem summable_norm_indexedHigherAction (s k : ℕ) (hk : k ≤ 2*s)
    (a : SobolevSource s) (ha : higherSobolevSourceInclusion s a ∈ U) :
    Summable (fun n : ℤ => ‖sourceIndexedHigherAction (by simp) (by norm_num) n k
      (higherSobolevSourceInclusion s a)‖) := by
  simpa only [Q.indexedHigherSobolevActionSequence_apply s k hk a ha] using
    (sourceIndexedHigherSobolevActionSequence s k a).property.norm.summable_of_one

/-- The literal infinite action sum is analytic on the full original complex Sobolev domain. -/
theorem analytic_tsum_indexedHigherAction (s k : ℕ) (hk : k ≤ 2*s) :
    AnalyticOnNhd ℂ (fun a : SobolevSource s => ∑' n : ℤ,
      sourceIndexedHigherAction (by simp) (by norm_num) n k (higherSobolevSourceInclusion s a))
      (higherSobolevSourceInclusion s ⁻¹' U) := by
  intro a ha
  have h := (lp.tsumCLM ℂ ℤ ℂ).comp_analyticOnNhd (Q.analytic_indexedHigherSobolevActionSequence s k hk) a ha
  apply h.congr
  filter_upwards [(Q.source_open.preimage (higherSobolevSourceInclusion s).continuous).mem_nhds ha] with b hb
  exact tsum_congr (Q.indexedHigherSobolevActionSequence_apply s k hk b hb)
end SourceSection19Data
end NLS.ZakharovShabat
