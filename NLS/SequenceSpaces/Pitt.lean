import NLS.SequenceSpaces.PittBlockContradiction
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! # Pitt's compactness theorem for complex coefficient spaces

Every bounded operator from a larger finite sequence exponent into a
smaller Banach sequence exponent is compact. The proof uses coefficient
subsequences and the disjoint-block growth contradiction.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- A bounded coefficient-null sequence becomes norm-null in a strictly
smaller sequence target under any bounded operator. -/
theorem tendsto_operator_of_bounded_coefficient_null
    (hp : p ≠ ⊤) (hqp : q < p) (T : Coeff p →L[ℂ] Coeff q)
    (x : ℕ → Coeff p) (hx : Bornology.IsBounded (range x))
    (hc : ∀ n, Tendsto (fun k => x k n) atTop (𝓝 0)) :
    Tendsto (fun k => T (x k)) atTop (𝓝 0) := by
  by_contra h
  rw [Metric.tendsto_atTop] at h
  push Not at h
  obtain ⟨ε,hε,hbad⟩ := h
  choose σ hσ hnorm using hbad
  have ht : Tendsto σ atTop atTop := tendsto_atTop_mono hσ tendsto_id
  apply not_lower_bound_image_of_bounded_coefficient_null hp hqp T (x ∘ σ)
    (hx.subset (range_comp_subset_range _ _)) (fun n => (hc n).comp ht) ε hε
  intro k
  simpa only [Function.comp_apply,dist_zero_right] using hnorm k

/-- Bounded coefficient convergence implies norm convergence of images
under every operator into a strictly smaller sequence exponent. -/
theorem tendsto_operator_of_bounded_coefficientwise
    (hp : p ≠ ⊤) (hqp : q < p) (T : Coeff p →L[ℂ] Coeff q)
    (x : ℕ → Coeff p) (hx : Bornology.IsBounded (range x)) (a : Coeff p)
    (hc : ∀ n, Tendsto (fun k => x k n) atTop (𝓝 (a n))) :
    Tendsto (fun k => T (x k)) atTop (𝓝 (T a)) := by
  obtain ⟨M,hM⟩ := hx.exists_norm_le
  have hb : Bornology.IsBounded (range (fun k => x k-a)) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨M+‖a‖,?_⟩
    rintro _ ⟨k,rfl⟩
    exact (norm_sub_le _ _).trans (add_le_add (hM _ ⟨k,rfl⟩) le_rfl)
  have hz : ∀ n, Tendsto (fun k => (x k-a) n) atTop (𝓝 0) := by
    intro n
    simpa only [lp.coeFn_sub,Pi.sub_apply,sub_self] using (hc n).sub_const (a n)
  have ht := (tendsto_operator_of_bounded_coefficient_null hp hqp T _ hb hz).add_const (T a)
  simpa only [map_sub,sub_add_cancel,zero_add] using ht

/-- Bounded operators into a smaller exponent send the closed unit ball
to a sequentially compact set. -/
theorem isSeqCompact_image_closedBall_of_exponent_lt
    (hp : p ≠ ⊤) (hqp : q < p) (T : Coeff p →L[ℂ] Coeff q) :
    IsSeqCompact (T '' closedBall (0 : Coeff p) 1) := by
  intro y hy
  choose x hx hxy using hy
  have hnorm (n : ℕ) : ‖x n‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx n
  have hb : Bornology.IsBounded (range x) := by
    apply isBounded_iff_forall_norm_le.mpr
    exact ⟨1,fun _ ⟨n,hn⟩ => hn ▸ hnorm n⟩
  obtain ⟨a,σ,hσ,hc⟩ := exists_coefficientwise_tendsto_subseq_of_bounded x hb
  have ha : ‖a‖ ≤ 1 := lp.norm_le_of_tendsto
    (Eventually.of_forall (fun n => hnorm (σ n))) (tendsto_pi_nhds.mpr hc)
  have ht := tendsto_operator_of_bounded_coefficientwise hp hqp T (x ∘ σ)
    (hb.subset (range_comp_subset_range _ _)) a hc
  refine ⟨T a,⟨a,by simpa only [mem_closedBall,dist_zero_right] using ha,rfl⟩,σ,hσ,?_⟩
  change Tendsto (fun k => T (x (σ k))) atTop (𝓝 (T a)) at ht
  have hefun : (fun k => T (x (σ k))) = y ∘ σ := funext (fun k => hxy (σ k))
  rw [hefun] at ht
  exact ht

/-- Pitt's theorem: every bounded operator from lp into lq is compact
when 1 <= q < p < infinity. The smaller target may equal one. -/
theorem isCompactOperator_of_exponent_lt
    (hp : p ≠ ⊤) (hqp : q < p) (T : Coeff p →L[ℂ] Coeff q) : IsCompactOperator T := by
  have hc : IsCompact (T '' closedBall (0 : Coeff p) 1) :=
    isCompact_iff_isSeqCompact.mpr (isSeqCompact_image_closedBall_of_exponent_lt hp hqp T)
  apply (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image
    (T : Coeff p → Coeff q)).mpr
  exact ⟨closedBall 0 1,closedBall_mem_nhds _ zero_lt_one,hc.closure⟩

end NLS.Coeff
