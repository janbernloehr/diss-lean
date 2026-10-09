import NLS.SequenceSpaces.Compact
import Mathlib.Topology.UniformSpace.Dini

/-! # Total boundedness from pointwise bounds and uniformly small tails -/
noncomputable section
open NLS Filter Set Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Enlarging the retained finite set decreases the omitted norm. -/
theorem norm_sub_truncate_mono (s t : Finset ℤ) (hst : s ⊆ t) (a : Coeff p) :
    ‖a-Coeff.truncate t a‖ ≤ ‖a-Coeff.truncate s a‖ := by
  apply lp.norm_mono (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out)))
  intro n
  by_cases hs : n ∈ s
  · simp [Coeff.truncate_apply,hs,hst hs]
  · by_cases ht : n ∈ t <;> simp [Coeff.truncate_apply,hs,ht]

/-- Finite-exponent Fourier truncations have uniformly small tails on compact sets. -/
theorem tendstoUniformlyOn_norm_tail_of_isCompact (hp : p ≠ ⊤) {K : Set (Coeff p)} (hK : IsCompact K) :
    TendstoUniformlyOn (fun s : Finset ℤ => fun a : Coeff p => ‖a-Coeff.truncate s a‖)
      (fun _ => (0 : ℝ)) atTop K := by
  apply Antitone.tendstoUniformlyOn_of_forall_tendsto hK
  · intro s
    exact (continuous_id.sub (Coeff.truncateCLM s).continuous).norm.continuousOn
  · intro a _ s t hst
    exact norm_sub_truncate_mono s t hst a
  · exact continuousOn_const
  · intro a _
    simpa using ((tendsto_const_nhds (x := a)).sub (Coeff.tendsto_truncate hp a)).norm

/-- Pointwise bounds and one uniformly bounded tail imply a global norm bound. -/
theorem isBounded_of_pointwise_tail {B : Set (Coeff p)}
    (hb : ∀ n : ℤ, ∃ C : ℝ, ∀ a ∈ B, ‖a n‖ ≤ C)
    (ht : ∃ s : Finset ℤ, ∀ a ∈ B, ‖a-Coeff.truncate s a‖ ≤ 1) :
    Bornology.IsBounded B := by
  classical
  choose C hC using hb
  obtain ⟨s,hs⟩ := ht
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1+∑ n ∈ s, C n,?_⟩
  intro a ha
  have hhead : ‖Coeff.truncate s a‖ ≤ ∑ n ∈ s, C n := by
    calc
      _ ≤ ∑ n ∈ s, ‖(lp.single p n (a n) : Coeff p)‖ := by
        exact norm_sum_le s (fun n => (lp.single p n (a n) : Coeff p))
      _ = ∑ n ∈ s, ‖a n‖ := by
        simp only [lp.norm_single (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))]
      _ ≤ _ := Finset.sum_le_sum (fun n _ => hC n a ha)
  calc
    ‖a‖ = ‖(a-Coeff.truncate s a)+Coeff.truncate s a‖ := by rw [sub_add_cancel]
    _ ≤ ‖a-Coeff.truncate s a‖+‖Coeff.truncate s a‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (hs a ha) hhead

/-- A bounded set with arbitrarily small uniform finite tails is totally bounded. -/
theorem totallyBounded_of_bounded_uniform_tails {B : Set (Coeff p)} (hb : Bornology.IsBounded B)
    (ht : ∀ ε : ℝ, 0 < ε → ∃ s : Finset ℤ, ∀ a ∈ B, ‖a-Coeff.truncate s a‖ ≤ ε) :
    TotallyBounded B := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨s,hs⟩ := ht (ε/2) (half_pos hε)
  have hK : IsCompact (closure ((Coeff.truncateCLM (p := p) s) '' B)) :=
    (Coeff.isCompactOperator_truncateCLM s).isCompact_closure_image_of_bounded hb
  obtain ⟨t,htfinite,htcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded (ε/2) (half_pos hε)
  refine ⟨t,htfinite,?_⟩
  intro a ha
  have hc := htcover (subset_closure (show Coeff.truncate s a ∈ (Coeff.truncateCLM (p := p) s) '' B from ⟨a,ha,rfl⟩))
  simp only [mem_iUnion] at hc ⊢
  obtain ⟨b,hb,hnear⟩ := hc
  refine ⟨b,hb,?_⟩
  rw [Metric.mem_ball] at hnear ⊢
  have hdist : dist a (Coeff.truncate s a) ≤ ε/2 := by
    simpa only [dist_eq_norm] using hs a ha
  have htri := dist_triangle a (Coeff.truncate s a) b
  linarith

/-- The finite-set form of I.3, for arbitrary sets and every finite Banach exponent. -/
theorem totallyBounded_iff_pointwise_uniform_finite_tails (hp : p ≠ ⊤) (B : Set (Coeff p)) :
    TotallyBounded B ↔
      (∀ n : ℤ, ∃ C : ℝ, ∀ a ∈ B, ‖a n‖ ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → ∃ s : Finset ℤ, ∀ a ∈ B, ‖a-truncate s a‖ ≤ ε) := by
  constructor
  · intro hB
    constructor
    · obtain ⟨C,hC⟩ := hB.isBounded.exists_norm_le
      intro n
      refine ⟨C,fun a ha => ?_⟩
      exact (lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) a n).trans (hC a ha)
    · have hK : IsCompact (closure B) := hB.closure.isCompact_of_isClosed isClosed_closure
      intro ε hε
      obtain ⟨s,hs⟩ := (Metric.tendstoUniformlyOn_iff.mp
        (tendstoUniformlyOn_norm_tail_of_isCompact hp hK) ε hε).exists
      refine ⟨s,fun a ha => ?_⟩
      simpa using (hs a (subset_closure ha)).le
  · rintro ⟨hb,ht⟩
    exact totallyBounded_of_bounded_uniform_tails (isBounded_of_pointwise_tail hb (ht 1 zero_lt_one)) ht

end NLS.Coeff
