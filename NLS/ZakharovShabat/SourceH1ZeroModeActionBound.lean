import NLS.ZakharovShabat.SourceH1EndpointActionBound
import NLS.ZakharovShabat.SourceActionExponentDifferential

/-! # Isolating the zero action in the H1 energy budget

The exact bracket weights give 2*M-I_0 <= S. If the central action is zero,
H3 <= S-M+S^2/2 without any smallness restriction. A collapsed zero gap
supplies this hypothesis, proving the literal endpoint of Lemma 27.2 on
that class. These are the original actions and physical Hamiltonian.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1:ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- The literal unweighted action summands form an absolutely convergent series. -/
theorem sourceWeightedActionTerm_zero_summable (ψ : realTypeSourceSubmodule 2) :
    Summable (sourceWeightedActionTerm ψ 0) := by
  have he : sourceWeightedActionTerm ψ 0 =
      (fun n => (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n).re) := by
    funext n
    simp only [sourceWeightedActionTerm,Nat.mul_zero,pow_zero,one_mul,norm_sourceRealAction]
  rw [he]
  exact sourceRealActions_summable ψ

/-- Every nonzero index has bracket weight at least two. -/
theorem two_mul_sourceAction_le_weighted_of_ne_zero (ψ : realTypeSourceSubmodule 2)
    (n : ℤ) (hn : n ≠ 0) :
    2*sourceWeightedActionTerm ψ 0 n ≤ sourceWeightedActionTerm ψ 1 n := by
  have hnabs : (1:ℝ) ≤ |(n:ℝ)| := by exact_mod_cast Int.one_le_abs hn
  have he : |((2*n:ℤ):ℝ)*Real.pi| = 2*|(n:ℝ)| *Real.pi := by
    simp only [Int.cast_mul,Int.cast_ofNat,abs_mul,abs_of_pos Real.pi_pos,
      abs_of_pos (by norm_num : (0:ℝ)<2)]
  have hbase : 1 ≤ |((2*n:ℤ):ℝ)*Real.pi| := by
    rw [he]
    nlinarith [Real.pi_gt_three,mul_le_mul_of_nonneg_right hnabs Real.pi_pos.le]
  have hw : (2:ℝ) ≤ (1+|((2*n:ℤ):ℝ)*Real.pi|)^2 := by nlinarith
  simpa only [sourceWeightedActionTerm,Nat.mul_zero,pow_zero,one_mul,Nat.mul_one]
    using mul_le_mul_of_nonneg_right hw
      (norm_nonneg (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n))

/-- Isolating the zero mode sharpens the weighted control of total action. -/
theorem sourceH1_two_mass_sub_zero_action_le_weighted (a : realTypeSobolevSourceLocus) :
    2*(∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n)-
      sourceWeightedActionTerm (sourceH1RealSource a) 0 0 ≤
      ∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n := by
  let I : ℤ → ℝ := sourceWeightedActionTerm (sourceH1RealSource a) 0
  let J : ℤ → ℝ := sourceWeightedActionTerm (sourceH1RealSource a) 1
  have hI : Summable I := sourceWeightedActionTerm_zero_summable _
  have hJ : Summable J := sourceH1_weightedActions_summable a
  have h0 := hasSum_ite_eq (0:ℤ) (I 0)
  have hb : ∀ n : ℤ, 2*I n ≤ J n+(if n=0 then I 0 else 0) := by
    intro n
    by_cases hn : n=0
    · subst n
      simp [I,J,sourceWeightedActionTerm,two_mul]
    · simpa only [if_neg hn,add_zero] using
        two_mul_sourceAction_le_weighted_of_ne_zero (sourceH1RealSource a) n hn
  have h := (hI.mul_left 2).tsum_le_tsum hb (hJ.add h0.summable)
  rw [tsum_mul_left,hJ.tsum_add h0.summable,h0.tsum_eq] at h
  change 2*(∑' n, I n)-I 0 ≤ ∑' n, J n
  linarith

/-- Inclusion into FL4 preserves each literal H1 action summand. -/
theorem sourceH1_actionTerm_zero_eq_FL4 (a : realTypeSobolevSourceLocus) (n : ℤ) :
    sourceWeightedActionTerm (sourceH1RealSource a) 0 n =
      ‖sourceComplexAction (by simp : (4:ℝ≥0∞) ≠ ⊤) (by norm_num) n (sobolevSourceFL4 a.val)‖ := by
  simp only [sourceWeightedActionTerm,Nat.mul_zero,pow_zero,one_mul]
  rw [← sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n
    (sourceH1RealSource a).val (sourceH1RealSource a).property]
  exact congrArg norm (sourceComplexAction_real_exponent (by simp) (by simp) (by norm_num) (by norm_num)
    (by norm_num : (2:ℝ≥0∞) ≤ 4) n (sourceH1RealSource a))

/-- With zero central action the actual energy has a global half-square remainder. -/
theorem sourceH1_energy_le_half_square_of_zero_action (a : realTypeSobolevSourceLocus)
    (hzero : sourceWeightedActionTerm (sourceH1RealSource a) 0 0 = 0) :
    (periodOneSobolevHamiltonian a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)-
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n)+
      (1/2:ℝ)*(∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)^2 := by
  have h := sourceH1_energy_le_weighted_actions_sub_mass a
  have hw := sourceH1_two_mass_sub_zero_action_le_weighted a
  rw [hzero,sub_zero] at hw
  have hm : 0 ≤ ∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n := by
    apply tsum_nonneg;intro n;unfold sourceWeightedActionTerm;positivity
  have hs : 0 ≤ ∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n := by linarith
  have hp := mul_nonneg
    (show 0 ≤ (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)-
      2*(∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n) by linarith)
    (show 0 ≤ (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)+
      2*(∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n) by positivity)
  nlinarith

/-- A collapsed zero gap supplies zero central action without any smallness assumption. -/
theorem sourceH1_zero_action_of_zero_gap (a : realTypeSobolevSourceLocus)
    (hgap : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sourceH1RealSource a).val)
      (periodOnePotential_mem (sourceH1RealSource a).val) 0 = 0) :
    sourceWeightedActionTerm (sourceH1RealSource a) 0 0 = 0 := by
  have ha := (sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num)
    (sourceH1RealSource a).val (sourceH1RealSource a).property 0).2.2.mpr
      (by simpa only [sourcePeriodicGapDisplacement_apply] using hgap)
  simp only [sourceWeightedActionTerm,ha,norm_zero,mul_zero]

/-- The literal m=1 endpoint holds globally when the central gap is collapsed. -/
theorem sourceH1_energy_le_lemma272_of_zero_gap (a : realTypeSobolevSourceLocus)
    (hgap : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sourceH1RealSource a).val)
      (periodOnePotential_mem (sourceH1RealSource a).val) 0 = 0) :
    (periodOneSobolevHamiltonian a.val).re ≤
      (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)+
      (1+∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)*
        (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n) := by
  have h := sourceH1_energy_le_half_square_of_zero_action a (sourceH1_zero_action_of_zero_gap a hgap)
  have hm : 0 ≤ ∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 0 n := by
    apply tsum_nonneg;intro n;unfold sourceWeightedActionTerm;positivity
  have hs : 0 ≤ ∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n := by
    apply tsum_nonneg;intro n;unfold sourceWeightedActionTerm;positivity
  nlinarith [sq_nonneg (∑' n : ℤ, sourceWeightedActionTerm (sourceH1RealSource a) 1 n)]

/-- A zero-mode square correction suffices for the scalar endpoint budget. -/
theorem energy_bound_of_zero_mode_correction (H M S I₀ U : ℝ)
    (hM : 0 ≤ M) (hIM : I₀ ≤ M) (hS : 2*M-I₀ ≤ S)
    (hU : I₀^2 ≤ U) (hH : H ≤ S-M+2*M^2-U) :
    H ≤ S-M+S^2 := by
  have hSM : M ≤ S := by linarith
  have hS0 : 0 ≤ S := hM.trans hSM
  have hp := mul_nonneg (show 0 ≤ S-(2*M-I₀) by linarith)
    (show 0 ≤ S+(2*M-I₀) by linarith)
  nlinarith [sq_nonneg (M-I₀)]

end NLS.ZakharovShabat
