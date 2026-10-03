import NLS.SequenceSpaces.ConjugateDuality
import NLS.SequenceSpaces.DominatedTails
import NLS.SequenceSpaces.CoefficientCompactness

/-! # Uniform duality limits from bounded coefficient convergence

Splitting bilinear duality into a finite head and a dominated tail makes
coefficient convergence uniform over every family with one norm-summable
coordinate majorant.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]

/-- Fourier truncation can be moved across the bilinear pairing. -/
theorem dualPairing_truncate_left (s : Finset ℤ) (a : Coeff p) (h : Coeff q) :
    dualPairing (truncate s a) h = dualPairing a (truncate s h) := by
  rw [dualPairing_apply,dualPairing_apply]
  apply tsum_congr
  intro n
  by_cases hn : n ∈ s <;> simp [truncate_apply,hn]

/-- A common majorant controls the finite head and the complementary
pairing, with smallness needed only in the majorant's tail. -/
theorem norm_dualPairing_le_head_tail (a b : Coeff p) (h : Coeff q)
    (hb : ∀ n : ℤ, ‖a n‖ ≤ ‖b n‖) (s : Finset ℤ) :
    ‖dualPairing a h‖ ≤ ‖b‖*‖truncate s h‖+‖b-truncate s b‖*‖h‖ := by
  have he : dualPairing a h = dualPairing a (truncate s h)+dualPairing (a-truncate s a) h := by
    rw [map_sub,sub_apply,dualPairing_truncate_left]
    abel
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add
    (norm_dualPairing_le a (truncate s h)) (norm_dualPairing_le (a-truncate s a) h)).trans
      (add_le_add
        (mul_le_mul_of_nonneg_right (lp.norm_mono (ne_of_gt (zero_lt_one.trans_le Fact.out)) hb) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (norm_sub_truncate_le_of_majorant a b hb s) (norm_nonneg _))))

/-- A bounded coefficient-null family pairs to zero uniformly over all
sequences dominated by one fixed finite-exponent majorant. -/
theorem eventually_small_dualPairing_of_bounded_coefficientwise
    (hp : p ≠ ⊤) {α : Type*} {l : Filter α} (h : α → Coeff q)
    (hbounded : Bornology.IsBounded (range h))
    (ht : ∀ n : ℤ, Tendsto (fun k => h k n) l (𝓝 0))
    (b : Coeff p) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k in l, ∀ a : Coeff p, (∀ n : ℤ, ‖a n‖ ≤ ‖b n‖) →
      ‖dualPairing a (h k)‖ < ε := by
  obtain ⟨M,hM⟩ := hbounded.exists_norm_le
  let B := max M 0+1
  have hB : 0 < B := by dsimp [B]; positivity
  have hbound (k : α) : ‖h k‖ ≤ B :=
    (hM _ ⟨k,rfl⟩).trans (by dsimp [B]; linarith [le_max_left M 0])
  obtain ⟨s,hs⟩ := (eventually_small_tails_of_majorant hp b (ε/(2*B)) (by positivity)).exists
  have htail : ‖b-truncate s b‖*B < ε/2 := by
    have ht' := hs b (fun _ => le_rfl)
    have hmul := (lt_div_iff₀ (by positivity : 0 < 2*B)).mp ht'
    nlinarith
  have hhead : Tendsto (fun k => ‖truncate s (h k)‖) l (𝓝 0) := by
    simpa [truncate] using (tendsto_truncate_of_coefficientwise h 0 (by simpa using ht) s).norm
  filter_upwards [hhead.eventually (gt_mem_nhds (show 0 < ε/(2*(‖b‖+1)) by positivity))] with k hk a ha
  have hhead' : ‖b‖*‖truncate s (h k)‖ < ε/2 := by
    have hmul := (lt_div_iff₀ (by positivity : 0 < 2*(‖b‖+1))).mp hk
    nlinarith [norm_nonneg (truncate s (h k))]
  have htail' : ‖b-truncate s b‖*‖h k‖ < ε/2 :=
    (mul_le_mul_of_nonneg_left (hbound k) (norm_nonneg _)).trans_lt htail
  exact (norm_dualPairing_le_head_tail a b (h k) ha s).trans_lt (by linarith)

end NLS.Coeff
