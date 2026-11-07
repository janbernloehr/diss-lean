import NLS.SequenceSpaces.TotalBoundedTails
import NLS.SequenceSpaces.FiniteExponentTail

/-! # Uniform coordinate tails after compact decoding

A continuous sequence map on an open weak domain has uniformly vanishing
coordinates on one fixed strong neighborhood after a compact linear map.
The neighborhood is chosen before the tail tolerance.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS

/-- Compact linear decoding puts one bounded open neighborhood inside a
compact subset of any prescribed open target neighborhood. -/
theorem exists_compact_decoded_neighborhood
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E →L[ℂ] F) (hL : IsCompactOperator L)
    {V : Set F} (hV : IsOpen V) (a : E) (ha : L a ∈ V) :
    ∃ U : Set E, IsOpen U ∧ a ∈ U ∧
      ∃ K : Set F, IsCompact K ∧ K ⊆ V ∧ L '' U ⊆ K := by
  obtain ⟨δ,hδ,hδV⟩ := Metric.isOpen_iff.mp hV (L a) ha
  let U := L ⁻¹' ball (L a) (δ/2) ∩ ball a 1
  have hU : IsOpen U := (isOpen_ball.preimage L.continuous).inter isOpen_ball
  have haU : a ∈ U := ⟨mem_ball_self (half_pos hδ),mem_ball_self zero_lt_one⟩
  have hb : Bornology.IsBounded U := isBounded_ball.subset inter_subset_right
  have hK : IsCompact (closure (L '' U)) := hL.isCompact_closure_image_of_bounded hb
  have hsub : closure (L '' U) ⊆ closedBall (L a) (δ/2) := by
    apply closure_minimal _ isClosed_closedBall
    rintro _ ⟨x,hx,rfl⟩
    exact ball_subset_closedBall hx.1
  exact ⟨U,hU,haU,closure (L '' U),hK,
    hsub.trans ((closedBall_subset_ball (half_lt_self hδ)).trans hδV),subset_closure⟩

namespace Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A compact set in a finite-exponent coefficient space has uniform
two-sided coordinate tails. -/
theorem exists_uniform_natAbs_norm_lt_of_isCompact (hp : p ≠ ⊤)
    {K : Set (Coeff p)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ a ∈ K, ∀ n : ℤ, N ≤ n.natAbs → ‖a n‖ < ε := by
  classical
  obtain ⟨s,hs⟩ := (Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_norm_tail_of_isCompact hp hK) ε hε).exists
  refine ⟨s.sup (fun n : ℤ => n.natAbs)+1,?_⟩
  intro a ha n hn
  have hnS : n ∉ s := by
    intro hnS
    have hle := Finset.le_sup (f := fun k : ℤ => k.natAbs) hnS
    omega
  have hrow := lp.norm_apply_le_norm
    (ne_of_gt (zero_lt_one.trans_le (show 1 ≤ p from Fact.out))) (a-truncate s a) n
  have hsmall : ‖a-truncate s a‖ < ε := by simpa using hs a ha
  simpa only [lp.coeFn_sub,Pi.sub_apply,truncate_apply,if_neg hnS,sub_zero]
    using hrow.trans_lt hsmall

/-- One fixed open strong neighborhood supports every uniform tail
tolerance for a continuous sequence map after compact decoding. -/
theorem exists_local_uniform_coordinate_tails_compact_pullback
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (hp : p ≠ ⊤) (L : E →L[ℂ] F) (hL : IsCompactOperator L)
    (f : F → Coeff p) {V : Set F} (hV : IsOpen V) (hf : ContinuousOn f V)
    (a : E) (ha : L a ∈ V) :
    ∃ U : Set E, IsOpen U ∧ a ∈ U ∧ L '' U ⊆ V ∧
      ∀ ε > (0:ℝ), ∃ N : ℕ, ∀ b ∈ U, ∀ n : ℤ,
        N ≤ n.natAbs → ‖f (L b) n‖ < ε := by
  obtain ⟨U,hU,haU,K,hK,hKV,hUK⟩ :=
    exists_compact_decoded_neighborhood L hL hV a ha
  have hQ : IsCompact (f '' K) := hK.image_of_continuousOn (hf.mono hKV)
  refine ⟨U,hU,haU,hUK.trans hKV,?_⟩
  intro ε hε
  obtain ⟨N,hN⟩ := exists_uniform_natAbs_norm_lt_of_isCompact hp hQ hε
  exact ⟨N,fun b hb n hn => hN _ ⟨L b,hUK ⟨b,hb,rfl⟩,rfl⟩ n hn⟩

end Coeff
end NLS
