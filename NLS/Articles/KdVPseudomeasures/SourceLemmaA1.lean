import NLS.SequenceSpaces.QuadraticReciprocalPower

/-! The sharp quadratic reciprocal bounds of Appendix A.1 in all three
exponent regimes. The constants precede every positive spectral index. -/
noncomputable section
open NLS.ReciprocalSeries
namespace NLS.Articles.KdVPseudomeasures

theorem sourceLemmaA_1_subcritical (s : ℝ) (hs : (1:ℝ)/2 < s) (hs1 : s < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      Summable (quadraticPowerKernel s n) ∧
      (∑' k : ℤ, quadraticPowerKernel s n k) ≤ C/(n:ℝ)^(2*s-1) := by
  have hd1 : 0<1-s := by linarith
  have hd2 : 0<2*s-1 := by linarith
  let C := (4*(2:ℝ)^s)*(1/(1-s)+1/(2*s-1))
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro n hn
  obtain ⟨hsum,hb⟩ := quadraticPowerKernel_twoScale_bound s hs n hn
  refine ⟨hsum,hb.trans ?_⟩
  have h := mul_le_mul_of_nonneg_left (subcritical_twoScale_sum s hs hs1 n hn).2
    (by positivity : 0 ≤ 4*(2:ℝ)^s)
  convert h using 1
  rw [show 1-2*s=-(2*s-1) by ring,Real.rpow_neg (by positivity : (0:ℝ)≤n)]
  dsimp [C]
  ring

theorem sourceLemmaA_1_supercritical (s : ℝ) (hs : 1 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      Summable (quadraticPowerKernel s n) ∧
      (∑' k : ℤ, quadraticPowerKernel s n k) ≤ C/(n:ℝ)^s := by
  let C := (4*(2:ℝ)^s)*(s/(s-1))
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro n hn
  have hnp : (0:ℝ)<n := by exact_mod_cast hn
  have hsNat : Summable (fun j : ℕ => ((j:ℝ)+1)^(-s)) :=
    summable_nat_shifted_rpow (by norm_num) hs
  have hbNat : (∑' j : ℕ, ((j:ℝ)+1)^(-s)) ≤ s/(s-1) := by
    simpa only [zero_add,add_zero,Real.one_rpow,mul_one] using
      tsum_nat_succ_shifted_rpow_le_simple (α:=0) (by norm_num) hs
  have htwo := summable_twoScalePower s (by linarith) n
  have hp : Summable (fun j : ℕ => ((j:ℝ)+1)^(-s)*((n:ℝ)+(j:ℝ)+1)^(-s)) := by
    simpa only [Function.comp_def,twoScalePower_positive] using
      htwo.comp_injective (i:=fun j : ℕ => (j:ℤ)+1) (by intro a b h; dsimp only at h; omega)
  have hb : (∑' j : ℕ, ((j:ℝ)+1)^(-s)*((n:ℝ)+(j:ℝ)+1)^(-s)) ≤
      (n:ℝ)^(-s)*(s/(s-1)) := by
    calc
      _ ≤ ∑' j : ℕ, (n:ℝ)^(-s)*((j:ℝ)+1)^(-s) := by
        apply hp.tsum_le_tsum _ (hsNat.mul_left _)
        intro j
        have h := Real.rpow_le_rpow_of_nonpos hnp
          (show (n:ℝ)≤(n:ℝ)+(j:ℝ)+1 by linarith [Nat.cast_nonneg (α:=ℝ) j])
          (by linarith : -s≤0)
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left h
          (Real.rpow_nonneg (by positivity : 0≤(j:ℝ)+1) (-s))
      _ = (n:ℝ)^(-s)*(∑' j : ℕ, ((j:ℝ)+1)^(-s)) := tsum_mul_left
      _ ≤ _ := mul_le_mul_of_nonneg_left hbNat (by positivity)
  obtain ⟨hsum,hkernel⟩ := quadraticPowerKernel_twoScale_bound s (by linarith) n hn
  refine ⟨hsum,hkernel.trans ?_⟩
  have h := mul_le_mul_of_nonneg_left hb (by positivity : 0≤4*(2:ℝ)^s)
  convert h using 1
  rw [Real.rpow_neg hnp.le]
  dsimp [C]
  ring

theorem sourceLemmaA_1_harmonic :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      Summable (quadraticPowerKernel 1 n) ∧
      (∑' k : ℤ, quadraticPowerKernel 1 n k) ≤ C*Real.log (1+(n:ℝ))/(n:ℝ) := by
  let L := Real.log 2
  have hL : 0 < L := Real.log_pos (by norm_num)
  let C := 8*Real.exp 1+12*Real.exp 1/L
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro n hn
  have hnp : (0:ℝ)<n := by exact_mod_cast hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast hn
  change Summable (mixedHillKernel 1 n) ∧
    (∑' k : ℤ, mixedHillKernel 1 n k) ≤ _
  refine ⟨summable_mixedHillKernel 1 (by norm_num) le_rfl n hn,?_⟩
  have hlog : 0 ≤ Real.log (1+(n:ℝ)) := Real.log_nonneg (by linarith)
  by_cases hl : 1 < Real.log (n:ℝ)
  · apply (tsum_hillKernel_one_le_log n hn hl).trans
    have hb : Real.log (n:ℝ) ≤ Real.log (1+(n:ℝ)) := Real.log_le_log hnp (by linarith)
    have hC : 8*Real.exp 1 ≤ C := by
      dsimp only [C]
      have h : 0 ≤ 12*Real.exp 1/L := by positivity
      linarith
    apply div_le_div_of_nonneg_right _ hnp.le
    exact mul_le_mul hC hb (by linarith) (by positivity)
  · have hne : (n:ℝ) ≤ Real.exp 1 := (Real.log_le_iff_le_exp hnp).mp (le_of_not_gt hl)
    have hcoarse : (∑' k : ℤ, mixedHillKernel 1 n k) ≤ 12 := by
      have h := tsum_mixedHillKernel_le 1 (by norm_num) le_rfl n hn
      norm_num only [div_one,add_self_div_two] at h
      have hp : (n:ℝ)^(-(1:ℝ)/2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
      exact h.trans (by nlinarith)
    apply hcoarse.trans
    have hb : L ≤ Real.log (1+(n:ℝ)) := Real.log_le_log (by norm_num) (by linarith)
    have hc : 0 ≤ 12*Real.exp 1/L := by positivity
    have hmul := mul_le_mul_of_nonneg_left hb hc
    have he : (12*Real.exp 1/L)*L=12*Real.exp 1 := div_mul_cancel₀ _ hL.ne'
    rw [he] at hmul
    apply (le_div_iff₀ hnp).mpr
    have hC : 12*Real.exp 1/L ≤ C := by
      dsimp only [C]
      have h : 0 < Real.exp 1 := Real.exp_pos 1
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hC hlog]

end NLS.Articles.KdVPseudomeasures
