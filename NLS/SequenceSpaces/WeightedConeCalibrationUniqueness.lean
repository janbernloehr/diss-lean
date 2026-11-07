import NLS.SequenceSpaces.WeightedNonnegativeActions

/-! Equality of continuous raw ell1 cone maps follows from calibration
on ANY weighted ell1 cone preserving raw coefficients. Finite raw
truncations belong to every positive weight, including infinite zero sets. -/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff

theorem eq_on_cone_of_weighted_calibration {F : Type*} [TopologicalSpace F] [T2Space F]
    (w : Weight) (J : WeightedCoeff w 1 → Coeff 1)
    (hJ : ∀ b : WeightedCoeff w 1, ∀ k : ℤ, J b k=b.val k)
    (U V : Set (Coeff 1)) (hU : IsOpen U) (hV : IsOpen V)
    (hCU : nonnegativeLocus 1⊆U) (hCV : nonnegativeLocus 1⊆V)
    (f g : Coeff 1 → F) (hf : ContinuousOn f U) (hg : ContinuousOn g V)
    (he : ∀ b : WeightedCoeff w 1, b∈WeightedCoeff.nonnegativeLocus w 1 → f (J b)=g (J b))
    (a : Coeff 1) (ha : a∈nonnegativeLocus 1) : f a=g a := by
  have ht := tendsto_truncate (by norm_num : (1 : ℝ≥0∞)≠⊤) a
  have hl := (hf.continuousAt (hU.mem_nhds (hCU ha))).tendsto.comp ht
  have hr := (hg.continuousAt (hV.mem_nhds (hCV ha))).tendsto.comp ht
  have hfinite (S : Finset ℤ) : f (truncate S a)=g (truncate S a) := by
    have hs : Summable (fun k : ℤ => ‖(w k : ℂ)*truncate S a k‖) :=
      summable_of_ne_finset_zero (s := S) (by intro k hk;simp only [truncate_apply,if_neg hk,mul_zero,norm_zero])
    have hm : Memℓp (fun k : ℤ => (w k : ℂ)*truncate S a k) 1 := by
      apply memℓp_gen
      simpa only [ENNReal.toReal_one,Real.rpow_one] using hs
    let b : WeightedCoeff w 1 := ⟨fun k => truncate S a k,hm⟩
    have hb : b∈WeightedCoeff.nonnegativeLocus w 1 := by
      intro k
      change ((truncate S a k).im=0 ∧ 0≤(truncate S a k).re)
      rw [truncate_apply]
      split_ifs
      · exact ha k
      · simp
    have hJb : J b=truncate S a := by ext k;exact hJ b k
    simpa only [hJb] using he b hb
  exact tendsto_nhds_unique hl (hr.congr' (Eventually.of_forall (fun S => (hfinite S).symm)))

end NLS.Coeff
