import NLS.KdV.HillMiuraGroundActions
import NLS.KdV.HillMiuraActionReflection
import NLS.KdV.HillMiuraFiniteGapEnergyBound

/-! # Ground-factor energy controlled by an actual normalized positive target

The positive coordinate calibration uses the original physical Hill
actions and the exact weight 1+n. Reflection handles negative indices;
the full Hilbert norm controls the finite spectral action sum.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

theorem hillMiura_finiteGap_energy_le_positive_target_norm
    (q : RealPeriodOneHillPotential) (u : PeriodOneRealL2) (e : ℝ) (hm : u.val 0 = 0)
    (hi : periodOneMiura u.val = hillOriginalHminusSource q.val+
      periodOneL2Inclusion (lp.single 2 0 (e : ℂ)))
    (hf : hillMiuraRealSource u ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (a : Coeff 2)
    (ha : ∀ n : ℕ, 0 < n → hillRealGapIntegral q.val q.property.1 q.property.2 n 0 =
      (1+(n : ℝ))*‖a (n : ℤ)‖^2) :
    ‖u.val‖^2 ≤ (2/Real.pi)*‖a‖^2 := by
  classical
  have hp (n : ℕ) (hn : 0 < n) :
      sourceRealHigherAction (by simp) (by norm_num) (hillMiuraRealSource u) n 1/(Real.pi*(n : ℝ)) ≤
        (1/Real.pi)*‖a (n : ℤ)‖^2 := by
    have hact := hillOriginal_action_eq_twice_ground_Dirac q u e hm hi n hn
    rw [ha n hn] at hact
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
    have he : sourceRealHigherAction (by simp) (by norm_num) (hillMiuraRealSource u) n 1 =
        (1+(n : ℝ))*‖a (n : ℤ)‖^2/2 := by linarith
    rw [he]
    calc
      _ = (1+(n : ℝ))*‖a (n : ℤ)‖^2/(2*Real.pi*(n : ℝ)) := by ring
      _ ≤ (2*(n : ℝ))*‖a (n : ℤ)‖^2/(2*Real.pi*(n : ℝ)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)) (by positivity)
      _ = _ := by field_simp
  have hbound (n : ℤ) :
      sourceRealHigherAction (by simp) (by norm_num) (hillMiuraRealSource u) n 1/(Real.pi*(n : ℝ)) ≤
        (1/Real.pi)*(‖a n‖^2+‖a (-n)‖^2) := by
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · let k := (-n).toNat
      have hk : 0 < k := by dsimp [k]; omega
      have hkn : (k : ℤ) = -n := by dsimp [k]; omega
      have hn' : n = -(k : ℤ) := by omega
      have hneg := hillMiura_realHigherAction_neg u (k : ℤ) 1
      simp only [pow_one,neg_one_mul] at hneg
      have he : sourceRealHigherAction (by simp) (by norm_num) (hillMiuraRealSource u) n 1/(Real.pi*(n : ℝ)) =
          sourceRealHigherAction (by simp) (by norm_num) (hillMiuraRealSource u) k 1/(Real.pi*(k : ℝ)) := by
        rw [hn',hneg]
        simp only [Int.cast_neg,Int.cast_natCast,mul_neg,neg_div_neg_eq]
      rw [he]
      have h := hp k hk
      have hnorm : ‖a (k : ℤ)‖^2 = ‖a (-n)‖^2 := by rw [hkn]
      rw [hnorm] at h
      exact h.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (sq_nonneg ‖a n‖)) (by positivity))
    · simp only [Int.cast_zero,mul_zero,div_zero,neg_zero]
      positivity
    · let k := n.toNat
      have hk : 0 < k := by dsimp [k]; omega
      have hkn : (k : ℤ) = n := by dsimp [k]; omega
      have h := hp k hk
      have hkR : (k : ℝ) = (n : ℝ) := by exact_mod_cast hkn
      rw [hkn,hkR] at h
      exact h.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg ‖a (-n)‖)) (by positivity))
  have hsum (b : Coeff 2) : (∑ n ∈ hf.toFinset, ‖b n‖^2) ≤ ‖b‖^2 := by
    have hs : Summable (fun n : ℤ => ‖b n‖^2) := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
        (lp.memℓp b).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    have he : ‖b‖^2 = ∑' n : ℤ, ‖b n‖^2 := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
        lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) b
    rw [he]
    exact hs.sum_le_tsum _ (fun _ _ => sq_nonneg _)
  have hs1 := hsum a
  have hs2 := hsum (Coeff.reflection a)
  change (∑ n ∈ hf.toFinset, ‖a (-n)‖^2) ≤ ‖Coeff.reflection a‖^2 at hs2
  rw [Coeff.reflection.norm_map] at hs2
  calc
    ‖u.val‖^2 ≤ ∑ n ∈ hf.toFinset,
        sourceRealHigherAction (by simp) (by norm_num) (hillMiuraRealSource u) n 1/(Real.pi*(n : ℝ)) :=
      hillMiura_finiteGap_norm_sq_le_weak_weighted_actions u hm hf
    _ ≤ ∑ n ∈ hf.toFinset, (1/Real.pi)*(‖a n‖^2+‖a (-n)‖^2) :=
      Finset.sum_le_sum (fun n _hn => hbound n)
    _ = (1/Real.pi)*((∑ n ∈ hf.toFinset, ‖a n‖^2)+(∑ n ∈ hf.toFinset, ‖a (-n)‖^2)) := by
      rw [←Finset.mul_sum,Finset.sum_add_distrib]
    _ ≤ (1/Real.pi)*(‖a‖^2+‖a‖^2) := mul_le_mul_of_nonneg_left (add_le_add hs1 hs2) (by positivity)
    _ = (2/Real.pi)*‖a‖^2 := by ring

end NLS.KdV
