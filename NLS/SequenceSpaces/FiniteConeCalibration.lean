import NLS.SequenceSpaces.NonnegativeActions

/-! Finite nonnegative actions determine continuous maps on the full
cone. Their real quadratic lifts retain the same finite support. -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem eq_on_cone_of_finite_calibration {F : Type*} [TopologicalSpace F] [T2Space F]
    (U V : Set (Coeff 1)) (hU : IsOpen U) (hV : IsOpen V)
    (hCU : nonnegativeLocus 1⊆U) (hCV : nonnegativeLocus 1⊆V)
    (f g : Coeff 1 → F) (hf : ContinuousOn f U) (hg : ContinuousOn g V)
    (he : ∀ a∈nonnegativeLocus 1, ∀ S : Finset ℤ,
      (∀ k∉S, a k=0) → f a=g a) (a : Coeff 1) (ha : a∈nonnegativeLocus 1) : f a=g a := by
  have ht := tendsto_truncate (by norm_num : (1 : ℝ≥0∞)≠⊤) a
  have hl := (hf.continuousAt (hU.mem_nhds (hCU ha))).tendsto.comp ht
  have hr := (hg.continuousAt (hV.mem_nhds (hCV ha))).tendsto.comp ht
  have hfinite (S : Finset ℤ) : f (truncate S a)=g (truncate S a) := by
    have hb : truncate S a∈nonnegativeLocus 1 := by
      intro k
      rw [truncate_apply]
      split_ifs
      · exact ha k
      · simp
    exact he _ hb S (fun k hk => by simp only [truncate_apply,if_neg hk])
  exact tendsto_nhds_unique hl (hr.congr' (Eventually.of_forall (fun S => (hfinite S).symm)))

theorem exists_finite_real_quadraticActions_lift (a : Coeff 1) (ha : a∈nonnegativeLocus 1)
    (S : Finset ℤ) (hS : ∀ k∉S, a k=0) :
    ∃ z : Coeff 2 × Coeff 2, z∈realPairLocus 2 ∧ quadraticActionsExponent (q := 1) z=a ∧
      ∀ k∉S, z.1 k=0 ∧ z.2 k=0 := by
  obtain ⟨z,hzr,hQ,hz2⟩ := exists_real_quadraticActions_lift (p := 2) (q := 1) (by norm_num) a ha
  refine ⟨z,hzr,hQ,?_⟩
  intro k hk
  have hq := congrArg (fun b : Coeff 1 => b k) hQ
  rw [quadraticActionsExponent_apply,hS k hk,hz2] at hq
  simp only [lp.coeFn_zero,Pi.zero_apply,zero_pow (by norm_num : 2≠0),add_zero,
    div_eq_zero_iff] at hq
  exact ⟨(sq_eq_zero_iff.mp ((hq.resolve_right (by norm_num)))),by simp only [hz2,lp.coeFn_zero,Pi.zero_apply]⟩

end NLS.Coeff
