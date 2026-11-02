import NLS.SequenceSpaces.FiniteHeadTailBound
import NLS.SequenceSpaces.LocallyBoundedAnalyticSummation

/-! # Analytic sums with finitely many uncontrolled coordinates -/
noncomputable section
open Set Filter Topology
namespace NLS.Coeff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A bounded l1 tail majorant and analytic scalar coordinates give an
analytic sum; finitely many head coordinates need no uniform global bound. -/
theorem analytic_tsum_of_bounded_one_tail
    (f : E → ℤ → ℂ) {U : Set E} (hU : IsOpen U)
    (ha : ∀ j, AnalyticOnNhd ℂ (fun q => f q j) U)
    (S : Finset ℤ) (b : E → Coeff 1) (B C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ q ∈ U, ‖b q‖ ≤ B)
    (htail : ∀ q ∈ U, ∀ j ∉ S, ‖f q j‖ ≤ C*‖b q j‖) :
    (∀ q ∈ U, Summable (fun j => ‖f q j‖)) ∧
      AnalyticOnNhd ℂ (fun q => ∑' j, f q j) U ∧
      TendstoLocallyUniformlyOn
        (fun (N : ℕ) q => ∑ j ∈ Finset.Icc (-(N : ℤ)) N, f q j)
        (fun q => ∑' j, f q j) atTop U := by
  apply analytic_tsum_of_local_one_bounds f hU ha
  intro x hx
  let H : E → ℝ := fun q => ∑ j ∈ S, ‖f q j‖
  have hc : ContinuousAt H x := by
    apply tendsto_finsetSum
    intro j _
    exact ((ha j x hx).continuousAt).norm
  have he : ∀ᶠ q in 𝓝 x, H q < H x+1 :=
    hc.eventually (gt_mem_nhds (by linarith : H x < H x+1))
  obtain ⟨W,hWsub,hW,hxW⟩ := _root_.mem_nhds_iff.mp he
  refine ⟨W ∩ U,hW.inter hU,⟨hxW,hx⟩,inter_subset_right,H x+1+C*B,?_⟩
  intro q hq
  have hh : ‖finiteHead (p := 1) S (f q)‖ ≤ H q := by
    dsimp only [finiteHead,H]
    exact (norm_sum_le _ _).trans_eq (by
      apply Finset.sum_congr rfl
      intro j _
      exact lp.norm_single (by norm_num : 0 < (1 : ENNReal)) _ _)
  obtain ⟨hmem,hnorm⟩ := memℓp_and_norm_ofFunctionOrZero_le_of_head_tail_bound
    (f q) (f q) S (b q) (0 : Coeff 1) C hC (fun _ _ => le_rfl)
    (fun j hj => by simpa only [lp.coeFn_zero,Pi.zero_apply,norm_zero,add_zero] using htail q hq.2 j hj)
  refine ⟨ofFunctionOrZero 1 (f q),fun j => ofFunctionOrZero_apply_of_mem 1 _ hmem j,?_⟩
  apply hnorm.trans
  simp only [norm_zero,add_zero]
  exact add_le_add (hh.trans (hWsub hq.1).le) (mul_le_mul_of_nonneg_left (hb q hq.2) hC)

end NLS.Coeff
