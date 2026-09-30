import NLS.SequenceSpaces.Truncation

/-!
# Locally uniform decay of a continuous sequence map

For a finite Banach exponent, norm continuity makes all sufficiently
distant coordinates small on one neighborhood. A single finite
truncation of the base sequence controls its tail, and the evaluation
maps bound every coordinate of the nearby sequence difference.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {X : Type*} [TopologicalSpace X]

theorem exists_local_uniform_small_coordinates
    (hp : p ≠ ⊤) (f : X → Coeff p) (x : X) (hf : ContinuousAt f x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ y ∈ V, ∀ n : ℤ, K < n.natAbs → ‖f y n‖ < ε := by
  classical
  obtain ⟨s,hs⟩ := Metric.tendsto_atTop.mp (tendsto_truncate hp (f x)) (ε/2) (half_pos hε)
  have hbase : ‖f x-truncate s (f x)‖ < ε/2 := by
    simpa only [dist_eq_norm,norm_sub_rev] using hs s le_rfl
  have hnear : ∀ᶠ y in 𝓝 x, ‖f y-f x‖ < ε/2 := by
    simpa only [mem_ball,dist_eq_norm] using
      hf.eventually (ball_mem_nhds (f x) (half_pos hε))
  obtain ⟨V,hVsub,hVopen,hxV⟩ := _root_.mem_nhds_iff.mp hnear
  let K := s.sup (fun n : ℤ => n.natAbs)
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  refine ⟨K,V,hVopen,hxV,?_⟩
  intro y hy n hn
  have hnot : n ∉ s := fun h => (not_le_of_gt hn) (Finset.le_sup h)
  have hxn : ‖f x n‖ < ε/2 := by
    have he := lp.norm_apply_le_norm hp0 (f x-truncate s (f x)) n
    simpa only [lp.coeFn_sub,Pi.sub_apply,truncate_apply,if_neg hnot,sub_zero] using he.trans_lt hbase
  have hyn : ‖f y n-f x n‖ < ε/2 :=
    (lp.norm_apply_le_norm hp0 (f y-f x) n).trans_lt (hVsub hy)
  have htri := norm_add_le (f y n-f x n) (f x n)
  rw [sub_add_cancel] at htri
  linarith

end NLS.Coeff
