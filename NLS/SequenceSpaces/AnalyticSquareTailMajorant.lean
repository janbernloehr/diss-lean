import NLS.SequenceSpaces.LocallyBoundedRealization
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Analytic ell1 realizations from locally bounded sampled ell2 tails

The finite head only needs coordinate analyticity. The tail may be
dominated by a different, nonanalytic ell2 sequence at each parameter,
provided its norm has a common local bound.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analytic_l1_realization_of_sampled_square_tail
    (f : E → ℤ → ℂ) (U : Set E) (hU : IsOpen U)
    (hf : ∀ k, AnalyticOnNhd ℂ (fun a => f a k) U)
    (s : Finset ℤ) (e : ℤ → ℤ) (he : Function.Injective e)
    (g : E → Coeff 2) (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hg : ∀ a ∈ U, ‖g a‖ ≤ B)
    (htail : ∀ a ∈ U, ∀ k ∉ s, ‖f a k‖ ≤ C*‖g a (e k)‖^2) :
    (∀ a ∈ U, ∀ k, ofFunctionOrZero 1 (f a) k = f a k) ∧
      AnalyticOnNhd ℂ (fun a => ofFunctionOrZero 1 (f a)) U := by
  classical
  apply analytic_realization_of_local_bounds f hU hf
  intro a ha
  have hhead : ∀ᶠ b in 𝓝 a, ∀ k ∈ s, ‖f b k‖ ≤ ‖f a k‖+1 := by
    apply (Filter.eventually_all_finset s).mpr
    intro k _
    exact (((hf k a ha).continuousAt.norm).eventually_lt_const (by linarith)).mono (fun _ hb => hb.le)
  obtain ⟨T,hTsub,hT,haT⟩ := _root_.mem_nhds_iff.mp hhead
  let H : ℤ → ℝ := fun k => if k ∈ s then ‖f a k‖+1 else 0
  have hHs : Summable H := summable_of_ne_finset_zero (s := s) (by intro k hk; simp [H,hk])
  have hH (k : ℤ) : 0 ≤ H k := by dsimp [H]; split_ifs <;> positivity
  refine ⟨T ∩ U,hT.inter hU,⟨haT,ha⟩,inter_subset_right,(∑' k, H k)+C*B^2,?_⟩
  intro b hb
  have hgs : Summable (fun k : ℤ => ‖g b k‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      (lp.memℓp (g b)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hsample : Summable (fun k => ‖g b (e k)‖^2) := hgs.comp_injective he
  let M : ℤ → ℝ := fun k => H k+C*‖g b (e k)‖^2
  have hMs : Summable M := hHs.add (hsample.mul_left C)
  have hbound (k : ℤ) : ‖f b k‖ ≤ M k := by
    by_cases hk : k ∈ s
    · exact (hTsub hb.1 k hk).trans (by
        dsimp only [M,H]
        rw [if_pos hk]
        exact le_add_of_nonneg_right (mul_nonneg hC (sq_nonneg _)))
    · simpa only [M,H,if_neg hk,zero_add] using htail b hb.2 k hk
  have hmem : Memℓp (f b) 1 := by
    apply memℓp_gen
    simpa only [ENNReal.toReal_one,Real.rpow_one] using
      hMs.of_nonneg_of_le (fun k => norm_nonneg (f b k)) hbound
  refine ⟨ofFunctionOrZero 1 (f b),fun k => ofFunctionOrZero_apply_of_mem _ _ hmem k,?_⟩
  have hnorm : ‖ofFunctionOrZero 1 (f b)‖ ≤ ∑' k, M k := by
    simpa only [ENNReal.toReal_one,Real.rpow_one] using
      norm_ofFunctionOrZero_rpow_le (p := 1) (by norm_num) (f b) M hMs (by
        intro k
        simpa only [ENNReal.toReal_one,Real.rpow_one] using hbound k)
  have hsum : (∑' k, ‖g b (e k)‖^2) ≤ B^2 := by
    calc
      _ ≤ ∑' k, ‖g b k‖^2 := tsum_comp_le_tsum_of_inj hgs (fun _ => sq_nonneg _) he
      _ = ‖g b‖^2 := by
        simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
          (lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (g b)).symm
      _ ≤ B^2 := (sq_le_sq₀ (norm_nonneg _) hB).mpr (hg b hb.2)
  apply hnorm.trans
  dsimp only [M]
  rw [hHs.tsum_add (hsample.mul_left C),tsum_mul_left]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum hC)

end NLS.Coeff
