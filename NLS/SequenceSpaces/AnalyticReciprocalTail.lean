import NLS.SequenceSpaces.LocallyBoundedRealization
import NLS.SequenceSpaces.FiniteHeadTailBound
import NLS.SequenceSpaces.PuncturedLattice

/-! # Analytic Hilbert realization from locally uniform reciprocal tails -/
noncomputable section
open Set Filter Topology
namespace NLS.Coeff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- An analytic finite head and locally uniform O(1/abs k) tails give
the actual l2 sequence and its Banach analyticity, with no fallback. -/
theorem analytic_l2_realization_of_local_reciprocal_tail
    (f : E → ℤ → ℂ) (U : Set E) (hU : IsOpen U)
    (ha : ∀ k, AnalyticOnNhd ℂ (fun x => f x k) U)
    (ht : ∀ x ∈ U, ∃ T : Set E, IsOpen T ∧ x ∈ T ∧ T ⊆ U ∧
      ∃ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧
        ∀ y ∈ T, ∀ k : ℤ, M < k.natAbs → ‖f y k‖ ≤ C/|(k : ℝ)|) :
    (∀ x ∈ U, ∀ k, ofFunctionOrZero 2 (f x) k = f x k) ∧
      AnalyticOnNhd ℂ (fun x => ofFunctionOrZero 2 (f x)) U := by
  apply analytic_realization_of_local_bounds f hU ha
  intro x hx
  obtain ⟨T,hT,hxT,hTU,M,C,hC,hbound⟩ := ht x hx
  let S : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)
  let H : E → Coeff 2 := fun y => finiteHead S (f y)
  have hH : ContinuousAt H x := by
    unfold H finiteHead
    apply tendsto_finsetSum S
    intro k _
    exact (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 k).continuous.continuousAt.comp
      (ha k x hx).continuousAt
  have hsmall : ∀ᶠ y in 𝓝 x, ‖H y‖ < ‖H x‖+1 :=
    hH.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨B,hBsub,hB,hxB⟩ := _root_.mem_nhds_iff.mp hsmall
  refine ⟨T ∩ B,hT.inter hB,⟨hxT,hxB⟩,fun _ hy => hTU hy.1,‖H x‖+1+2*C,?_⟩
  intro y hy
  have htail (k : ℤ) (hk : k ∉ S) :
      ‖f y k‖ ≤ C*(‖puncturedLattice 2 (by norm_num) k‖+‖(0 : Coeff 2) k‖) := by
    have hkm : M < k.natAbs := by
      simp only [S,Finset.mem_Icc] at hk
      omega
    have hk0 : k ≠ 0 := by omega
    simpa only [puncturedLattice_apply,if_neg hk0,norm_inv,Complex.norm_intCast,
      lp.coeFn_zero,Pi.zero_apply,norm_zero,add_zero,div_eq_mul_inv] using hbound y hy.1 k hkm
  obtain ⟨hmem,hnorm⟩ := memℓp_and_norm_ofFunctionOrZero_le_of_head_tail_bound
    (f y) (f y) S (puncturedLattice 2 (by norm_num)) 0 C hC (fun _ _ => le_rfl) htail
  refine ⟨ofFunctionOrZero 2 (f y),ofFunctionOrZero_apply_of_mem 2 _ hmem,?_⟩
  have hHy : ‖H y‖ < ‖H x‖+1 := hBsub hy.2
  have hp := norm_puncturedLattice_two_le
  simpa only [H,norm_zero,add_zero] using hnorm.trans (by
    change ‖H y‖+C*(‖puncturedLattice 2 (by norm_num)‖+‖(0 : Coeff 2)‖) ≤ _
    rw [norm_zero,add_zero]
    nlinarith)

end NLS.Coeff
