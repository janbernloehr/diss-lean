import NLS.ZakharovShabat.AppendixDDiscSupProduct
import NLS.ZakharovShabat.AppendixDDeletedRelativeProduct

/-! # The sum of squared factor suprema in the proof of D.6 -/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Taking the supremum of each factor preserves the reciprocal-square row bound. -/
theorem appendixDReciprocalTerm_discSup_square_sum_le (hp1 : 1 < p) (hp : p ≠ ⊤)
    (r : Coeff ⊤) (a : Coeff p) {c : ℝ} {N : ℕ}
    (hc : 0 < c) (hsep : AppendixDReferenceSeparated r c N)
    {n : ℤ} (hn : N ≤ n.natAbs) :
    (∑' m : ℤ, (appendixDDiscNormSup n
      (fun z => appendixDReciprocalTerm r a n z m))^2) ≤
        c^2*(∑' m : ℤ, ‖a m‖^2*‖NLS.Fourier.hilbertKernel (n-m)‖^2) := by
  obtain ⟨Q,hQ,_⟩ := NLS.Fourier.exists_squaredAbsoluteRows hp1 hp a
  have hs := (appendixDReciprocalTerm_discSup_summable hp r a hc hsep hn).2.2.1
  have hpoint (m : ℤ) : (appendixDDiscNormSup n
      (fun z => appendixDReciprocalTerm r a n z m))^2 ≤
        c^2*(‖a m‖^2*‖NLS.Fourier.hilbertKernel (n-m)‖^2) := by
    have hb := appendixDDiscNormSup_bounds n
      (fun z => appendixDReciprocalTerm r a n z m)
      (fun z hz => (appendixDReciprocalTerm_bounds hp r a hc hsep hn hz).2.2 m)
    calc
      _ ≤ (c*(‖a m‖*‖NLS.Fourier.hilbertKernel (n-m)‖))^2 :=
        pow_le_pow_left₀ hb.1 hb.2.2 2
      _ = _ := by ring
  simpa only [tsum_mul_left] using hs.tsum_le_tsum hpoint ((hQ n).1.mul_left (c^2))

/-- The literal square-supremum sum has half-exponent energy with c^p, also below p=2. -/
theorem appendixDReciprocalTerm_discSup_square_power_bound (hp1 : 1 < p) (hp : p ≠ ⊤)
    (r : Coeff ⊤) (a : Coeff p) {c : ℝ} {N : ℕ}
    (hc : 0 < c) (hsep : AppendixDReferenceSeparated r c N) :
    let B := fun n : ℤ => if N ≤ n.natAbs then
      ∑' m : ℤ, (appendixDDiscNormSup n
        (fun z => appendixDReciprocalTerm r a n z m))^2 else 0
    Memℓp (fun n => ((B n):ℂ)) (p/2) ∧
      Summable (fun n => (B n)^((p/2).toReal)) ∧
      (∑' n, (B n)^((p/2).toReal)) ≤
        c^p.toReal*‖a‖^p.toReal*
          (NLS.Fourier.squaredAbsoluteRowConstant hp1 hp)^((p/2).toReal) := by
  intro B
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  have hq : 0 < (p/2).toReal := by
    simp only [ENNReal.toReal_div,ENNReal.toReal_ofNat]
    positivity
  have hq0 : p/2 ≠ 0 := (ENNReal.toReal_pos_iff.mp hq).1.ne'
  have hC : 0 ≤ NLS.Fourier.squaredAbsoluteRowConstant hp1 hp := lp.norm_nonneg' _
  obtain ⟨Q,hQ,hQn⟩ := NLS.Fourier.exists_squaredAbsoluteRows hp1 hp a
  let T : Coeff (p/2) := ((c^2:ℝ):ℂ) • Q
  have hT (n : ℤ) : ‖T n‖ = c^2*‖Q n‖ := by
    simp only [T,lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,
      Real.norm_of_nonneg (sq_nonneg c)]
  have hB0 (n : ℤ) : 0 ≤ B n := by
    dsimp only [B]
    split_ifs
    · exact tsum_nonneg (fun _ => sq_nonneg _)
    · exact le_rfl
  have hB (n : ℤ) : ‖((B n):ℂ)‖ ≤ ‖T n‖ := by
    rw [Complex.norm_real,Real.norm_of_nonneg (hB0 n),hT]
    by_cases hn : N ≤ n.natAbs
    · change (if N ≤ n.natAbs then _ else _) ≤ _
      rw [if_pos hn]
      have hb := appendixDReciprocalTerm_discSup_square_sum_le hp1 hp r a hc hsep hn
      rw [(hQ n).2,Complex.norm_real,Real.norm_of_nonneg
        (tsum_nonneg (fun _ => by positivity))]
      exact hb
    · simp only [B,if_neg hn]
      positivity
  have hmem : Memℓp (fun n => ((B n):ℂ)) (p/2) := (lp.memℓp T).mono' hB
  let b : Coeff (p/2) := ⟨fun n => ((B n):ℂ),hmem⟩
  have hb (n : ℤ) : ‖b n‖ = B n := by
    change ‖((B n):ℂ)‖ = B n
    rw [Complex.norm_real,Real.norm_of_nonneg (hB0 n)]
  have hbn : ‖b‖ ≤ c^2*(‖a‖^2*NLS.Fourier.squaredAbsoluteRowConstant hp1 hp) := by
    calc
      _ ≤ ‖T‖ := lp.norm_mono hq0 hB
      _ = c^2*‖Q‖ := by
        change ‖((c^2:ℝ):ℂ) • Q‖ = _
        rw [lp.norm_const_smul hq0,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg c)]
      _ ≤ _ := mul_le_mul_of_nonneg_left hQn (sq_nonneg c)
  have hpow (x : ℝ) (hx : 0 ≤ x) : (x^2)^((p/2).toReal) = x^p.toReal := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hx]
    congr 1
    simp only [ENNReal.toReal_div,ENNReal.toReal_ofNat]
    ring
  refine ⟨hmem,by simpa only [hb] using b.property.summable hq,?_⟩
  calc
    _ = ‖b‖^((p/2).toReal) := by
      rw [lp.norm_rpow_eq_tsum hq]
      simp only [hb]
    _ ≤ (c^2*(‖a‖^2*NLS.Fourier.squaredAbsoluteRowConstant hp1 hp))^((p/2).toReal) :=
      Real.rpow_le_rpow (lp.norm_nonneg' b) hbn hq.le
    _ = _ := by
      rw [Real.mul_rpow (sq_nonneg c) (mul_nonneg (sq_nonneg ‖a‖) hC),
        Real.mul_rpow (sq_nonneg ‖a‖) hC,hpow c hc.le,hpow ‖a‖ (norm_nonneg _)]
      ring

end NLS.ZakharovShabat
