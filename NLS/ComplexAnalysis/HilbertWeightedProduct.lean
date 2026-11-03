import NLS.SequenceSpaces.UniformHolderTails
import NLS.SequenceSpaces.UniformHolderSums
import NLS.ComplexAnalysis.LocalAnalyticApproximationOn
import NLS.ComplexAnalysis.BanachSmoothAnalyticOn
import NLS.ComplexAnalysis.AbsoluteProductConvergence

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS.ComplexAnalysis



def hilbertWeightedProduct (b a : Coeff 2) : ℂ :=
  ∏' m : ℤ, (1+a m*b m)

def hilbertWeightedPartialProduct (b : Coeff 2) (N : ℕ) (a : Coeff 2) : ℂ :=
  ∏ m ∈ Finset.Icc (-(N : ℤ)) N, (1+a m*b m)

theorem summable_norm_hilbertProductInput (b a : Coeff 2) :
    Summable (fun m : ℤ => ‖a m*b m‖) := by
  have h := lp.tsum_mul_le_mul_norm
    (show (2 : ℝ≥0∞).toReal.HolderConjugate (2 : ℝ≥0∞).toReal from
      Real.HolderConjugate.two_two) a b
  simpa only [norm_mul] using h.1

theorem multipliable_hilbertWeightedFactors (b a : Coeff 2) :
    Multipliable (fun m : ℤ => (1+a m*b m)) :=
  multipliable_one_add_of_summable (summable_norm_hilbertProductInput b a)

theorem tendsto_hilbertWeightedPartialProduct (b a : Coeff 2) :
    Tendsto (fun N => hilbertWeightedPartialProduct b N a) atTop
      (𝓝 (hilbertWeightedProduct b a)) := by
  exact (multipliable_hilbertWeightedFactors b a).hasProd.comp Finset.tendsto_Icc_neg

theorem tendstoUniformlyOn_hilbertWeightedPartialProduct (b : Coeff 2)
    (S : Set (Coeff 2)) (R : ℝ) (hb : ∀ a ∈ S, ‖a‖ ≤ R) :
    TendstoUniformlyOn (hilbertWeightedPartialProduct b)
      (hilbertWeightedProduct b) atTop S := by
  have hc := Coeff.uniformCauchySeqOn_holder_products (fun a : Coeff 2 => a) b
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (fun a m => a m*b m) S 1 R (by norm_num) hb
    (fun a _ m => by simp only [one_mul]; rfl)
  exact hc.tendstoUniformlyOn_of_tendsto
    (fun a _ => tendsto_hilbertWeightedPartialProduct b a)

theorem analyticOnNhd_hilbertWeightedPartialProduct (b : Coeff 2) (N : ℕ) :
    AnalyticOnNhd ℂ (hilbertWeightedPartialProduct b N) univ := by
  intro a _
  apply (Finset.Icc (-(N : ℤ)) (N : ℤ)).analyticAt_fun_prod
  intro m _
  have he : AnalyticAt ℂ (fun c : Coeff 2 => c m) a :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m).analyticAt a
  exact analyticAt_const.add (he.mul analyticAt_const)

theorem analyticOnNhd_hilbertWeightedProduct (b : Coeff 2) :
    AnalyticOnNhd ℂ (hilbertWeightedProduct b) univ := by
  have hu (a : Coeff 2) (_ : a ∈ (univ : Set (Coeff 2))) :
      ∃ U : Set (Coeff 2), IsOpen U ∧ a ∈ U ∧
        TendstoUniformlyOn (hilbertWeightedPartialProduct b)
          (hilbertWeightedProduct b) atTop U := by
    refine ⟨ball a 1,isOpen_ball,mem_ball_self (by norm_num),?_⟩
    apply tendstoUniformlyOn_hilbertWeightedPartialProduct b (ball a 1) (‖a‖+1)
    intro c hc
    have hd : ‖c-a‖ < 1 := by simpa only [mem_ball,dist_eq_norm] using hc
    have he := norm_add_le (c-a) a
    rw [sub_add_cancel] at he
    linarith
  have ha := HasLocalUniformAnalyticApproximationOn.of_open_local_uniform isOpen_univ
    (analyticOnNhd_hilbertWeightedPartialProduct b) hu
  exact analyticOnNhd_of_complexSmoothOn _ isOpen_univ ha.contDiffOn

theorem hilbertWeightedProduct_ne_zero_iff (b a : Coeff 2) :
    hilbertWeightedProduct b a ≠ 0 ↔ ∀ m : ℤ, 1+a m*b m ≠ 0 :=
  tprod_one_add_ne_zero_iff (fun m : ℤ => a m*b m) (summable_norm_hilbertProductInput b a)

theorem norm_hilbertWeightedProduct_le (b a : Coeff 2) :
    ‖hilbertWeightedProduct b a‖ ≤ Real.exp (‖a‖*‖b‖) := by
  apply le_of_tendsto (multipliable_hilbertWeightedFactors b a).hasProd.norm
  filter_upwards with S
  simpa only [norm_prod] using (norm_prod_one_add_le_exp S (fun m => a m*b m)).trans
    (Real.exp_le_exp.mpr (Coeff.sum_norm_holderProduct_le a b S))

theorem norm_hilbertWeightedProduct_sub_one_le (b a : Coeff 2) :
    ‖hilbertWeightedProduct b a-1‖ ≤ Real.exp (‖a‖*‖b‖)-1 := by
  apply le_of_tendsto ((multipliable_hilbertWeightedFactors b a).hasProd.sub_const 1).norm
  filter_upwards with S
  exact (S.norm_prod_one_add_sub_one_le (fun m => a m*b m)).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr (Coeff.sum_norm_holderProduct_le a b S)) 1)

end NLS.ComplexAnalysis
