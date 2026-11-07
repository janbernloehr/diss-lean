import NLS.SequenceSpaces.SobolevHomogeneous
import NLS.SequenceSpaces.FourierTail
import NLS.ZakharovShabat.Domain

/-! Quantitative H1 Fourier heads and L2 remainders for fractional
Sobolev inputs. The boundary |k|=N belongs to the remainder. -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff

theorem sobolev_head_weight_bound (s : ℝ) (hs1 : s≤1) (N : ℕ) (hN : 1≤N) (k : ℤ) :
    Weight.sobolev 1 k*‖if k.natAbs<N then (1:ℂ) else 0‖ ≤
      (N:ℝ)^(1-s)*Weight.sobolev s k := by
  by_cases hk : k.natAbs<N
  · rw [if_pos hk,norm_one,mul_one]
    have hidx : (k.natAbs:ℝ)=|(k:ℝ)| := by
      simpa only [Int.cast_natCast,Int.cast_abs] using
        congrArg (fun j : ℤ => (j:ℝ)) (Int.natCast_natAbs k)
    have hbase : 1+|(k:ℝ)|≤(N:ℝ) := by
      rw [← hidx]
      exact_mod_cast (show 1+k.natAbs≤N by omega)
    have hpow := Real.rpow_le_rpow (by positivity : (0:ℝ)≤1+|(k:ℝ)|) hbase (sub_nonneg.mpr hs1)
    rw [Weight.sobolev_apply,Weight.sobolev_apply,Real.rpow_one]
    calc
      _ = (1+|(k:ℝ)|)^(1-s)*(1+|(k:ℝ)|)^s := by
        rw [← Real.rpow_add (by positivity),sub_add_cancel,Real.rpow_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (by positivity) s)
  · rw [if_neg hk,norm_zero,mul_zero]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) ((Weight.sobolev s).positive k).le

def sobolevHeadToH1 (s : ℝ) (hs1 : s≤1) (N : ℕ) (hN : 1≤N) :
    WeightedCoeff (Weight.sobolev s) 2 →L[ℂ] ZakharovShabat.ScalarDomain 2 :=
  weightedMultiplierCLM _ _ (fun k => if k.natAbs<N then 1 else 0)
    ((N:ℝ)^(1-s)) (Real.rpow_nonneg (by positivity) _) (sobolev_head_weight_bound s hs1 N hN)

theorem sobolevHeadToH1_apply (s : ℝ) (hs1 : s≤1) (N : ℕ) (hN : 1≤N)
    (u : WeightedCoeff (Weight.sobolev s) 2) (k : ℤ) :
    (sobolevHeadToH1 s hs1 N hN u).val k=if k.natAbs<N then u.val k else 0 := by
  change (if k.natAbs<N then (1:ℂ) else 0)*u.val k=_
  split_ifs <;> simp only [one_mul,zero_mul]

theorem norm_sobolevHeadToH1_le (s : ℝ) (hs1 : s≤1) (N : ℕ) (hN : 1≤N)
    (u : WeightedCoeff (Weight.sobolev s) 2) :
    ‖sobolevHeadToH1 s hs1 N hN u‖≤(N:ℝ)^(1-s)*‖u‖ :=
  norm_weightedMultiplier_le _ _ _ _ (Real.rpow_nonneg (by positivity) _)
    (sobolev_head_weight_bound s hs1 N hN) u

theorem scalarInclusion_sobolevHeadToH1 (s : ℝ) (hs : 0≤s) (hs1 : s≤1) (N : ℕ) (hN : 1≤N)
    (u : WeightedCoeff (Weight.sobolev s) 2) :
    ZakharovShabat.scalarInclusion (sobolevHeadToH1 s hs1 N hN u)=
      Coeff.truncate (Coeff.lowFrequencies N) (sobolevToL2 hs u) := by
  ext k
  simp only [ZakharovShabat.scalarInclusion_apply,sobolevHeadToH1_apply,
    Coeff.truncate_apply,Coeff.mem_lowFrequencies,sobolevToL2_apply]

theorem norm_scalarInclusion_sobolevHeadToH1_le (s : ℝ) (hs : 0≤s) (hs1 : s≤1) (N : ℕ) (hN : 1≤N)
    (u : WeightedCoeff (Weight.sobolev s) 2) :
    ‖ZakharovShabat.scalarInclusion (sobolevHeadToH1 s hs1 N hN u)‖≤‖sobolevToL2 hs u‖ := by
  rw [scalarInclusion_sobolevHeadToH1 s hs hs1 N hN u]
  exact Coeff.norm_truncate_le (by norm_num) _ _

theorem norm_sobolevHeadToH1_remainder_le (s : ℝ) (hs : 0≤s) (hs1 : s≤1) (N : ℕ) (hN : 1≤N)
    (u : WeightedCoeff (Weight.sobolev s) 2) :
    ‖sobolevToL2 hs u-ZakharovShabat.scalarInclusion (sobolevHeadToH1 s hs1 N hN u)‖≤
      (N:ℝ)^(-s)*‖u‖ := by
  rw [scalarInclusion_sobolevHeadToH1 s hs hs1 N hN u]
  have hNp : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hpoint (k : ℤ) :
      ‖(sobolevToL2 hs u-Coeff.truncate (Coeff.lowFrequencies N) (sobolevToL2 hs u)) k‖ ≤
        ‖(((N:ℝ)^(-s):ℝ):ℂ)*weightEquiv (Weight.sobolev s) 2 u k‖ := by
    simp only [lp.coeFn_sub,Pi.sub_apply,Coeff.truncate_apply,Coeff.mem_lowFrequencies,sobolevToL2_apply]
    by_cases hk : k.natAbs<N
    · rw [if_pos hk,sub_self,norm_zero]
      exact norm_nonneg _
    · rw [if_neg hk,sub_zero,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg hNp.le _),
        weightEquiv_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg ((Weight.sobolev s).positive k).le]
      have hidx : (k.natAbs:ℝ)=|(k:ℝ)| := by
        simpa only [Int.cast_natCast,Int.cast_abs] using
          congrArg (fun j : ℤ => (j:ℝ)) (Int.natCast_natAbs k)
      have hbase : (N:ℝ)≤1+|(k:ℝ)| := by
        have hle : (N:ℝ)≤k.natAbs := by exact_mod_cast (Nat.le_of_not_gt hk)
        rw [hidx] at hle
        linarith
      have hpow := Real.rpow_le_rpow hNp.le hbase hs
      have hw : 1≤(N:ℝ)^(-s)*Weight.sobolev s k := by
        calc
          1 = (N:ℝ)^(-s)*(N:ℝ)^s := by
            rw [← Real.rpow_add hNp,neg_add_cancel,Real.rpow_zero]
          _ ≤ _ := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hNp.le _)
      have h := mul_le_mul_of_nonneg_right hw (norm_nonneg (u.val k))
      simpa only [one_mul,mul_assoc] using h
  have hnorm : ‖sobolevToL2 hs u-Coeff.truncate (Coeff.lowFrequencies N) (sobolevToL2 hs u)‖ ≤
      ‖(((N:ℝ)^(-s):ℝ):ℂ) • weightEquiv (Weight.sobolev s) 2 u‖ :=
    lp.norm_mono (by norm_num : (2:ℝ≥0∞)≠0) hpoint
  simpa only [norm_smul,Complex.norm_real,Real.norm_of_nonneg (Real.rpow_nonneg hNp.le _),
    ← norm_eq] using hnorm

end NLS.WeightedCoeff
