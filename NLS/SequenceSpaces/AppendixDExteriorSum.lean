import NLS.SequenceSpaces.ReciprocalNorm
import NLS.SequenceSpaces.ReciprocalTail
import NLS.SequenceSpaces.HolderEmbedding

/-! # Height bounds for the scalar far/near sum in the proof of D.5 -/
noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A reciprocal envelope has the height decay used by D.5, including p=1. -/
theorem norm_appendixDReciprocalEnvelope_le (hp : p ≠ ⊤) {h : ℝ} (hh : 1 ≤ h)
    (a : Coeff p.conjExponent)
    (ha : ∀ k : ℤ, ‖a k‖ ≤ (h+|(k:ℝ)|)⁻¹) :
    ‖a‖ ≤ (4*p.toReal+1)*h^(-(1/p.toReal)) := by
  have hh0 : 0 < h := zero_lt_one.trans_le hh
  have hp1 : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hp (show 1 ≤ p from Fact.out)
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  by_cases hpe : p = 1
  · subst p
    have hbound : ‖a‖ ≤ h⁻¹ := by
      have htop : (1:ℝ≥0∞).conjExponent = ⊤ := by simp [ENNReal.conjExponent]
      revert a
      rw [htop]
      intro a ha
      apply lp.norm_le_of_forall_le (inv_nonneg.mpr hh0.le)
      intro k
      exact (ha k).trans (inv_anti₀ hh0 (by linarith [abs_nonneg (k:ℝ)]))
    norm_num only [ENNReal.toReal_one,mul_one,div_one,Real.rpow_neg_one]
    nlinarith [inv_nonneg.mpr hh0.le]
  · have hpgt : 1 < p := lt_of_le_of_ne Fact.out (Ne.symm hpe)
    have hq : p.conjExponent ≠ ⊤ := ne_of_lt
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hpgt)
    have hc := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
    have hb := norm_reciprocal_le hc hh0 a
      (by simpa only [Int.cast_zero,abs_zero,add_zero] using ha 0)
      (fun k _ => (ha k).trans (by rw [inv_eq_one_div]; gcongr; norm_num))
    have he : h⁻¹ ≤ h^(-(1/p.toReal)) := by
      rw [← Real.rpow_neg_one]
      apply Real.rpow_le_rpow_of_exponent_le hh
      have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp1
      have hv : 1/p.toReal ≤ 1 := (div_le_one hp0).mpr hp1
      linarith
    rw [Real.rpow_neg hh0.le] at he ⊢
    rw [div_eq_mul_inv] at hb
    nlinarith

/-- The actual reciprocal envelope in the conjugate sequence space. -/
def appendixDReciprocalEnvelope (hp : p ≠ ⊤) {h : ℝ} (hh : 1 ≤ h) :
    Coeff p.conjExponent :=
  ⟨fun k => ((h+|(k:ℝ)|:ℝ):ℂ)⁻¹, by
    apply (Weight.inverse_sobolev_one_memlp
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)).mono'
    intro k
    simp only [norm_inv,Complex.norm_real,Real.norm_eq_abs,Weight.sobolev_apply,
      Real.rpow_one,abs_of_pos (by positivity : 0 < 1+|(k:ℝ)|),
      abs_of_pos (by linarith [abs_nonneg (k:ℝ)] : 0 < h+|(k:ℝ)|)]
    exact inv_anti₀ (by positivity) (by linarith)⟩

@[simp] theorem norm_appendixDReciprocalEnvelope_apply (hp : p ≠ ⊤)
    {h : ℝ} (hh : 1 ≤ h) (k : ℤ) :
    ‖appendixDReciprocalEnvelope hp hh k‖ = (h+|(k:ℝ)|)⁻¹ := by
  simp only [appendixDReciprocalEnvelope,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (by linarith [abs_nonneg (k:ℝ)] : 0 < h+|(k:ℝ)|)]

/-- The complete absolute reciprocal sum has quantitative height decay. -/
theorem appendixDReciprocalSum_height_bound (hp : p ≠ ⊤) {h : ℝ} (hh : 1 ≤ h)
    (a : Coeff p) (n : ℤ) :
    Summable (fun m : ℤ => ‖a m‖/(h+|((m-n:ℤ):ℝ)|)) ∧
      (∑' m : ℤ, ‖a m‖/(h+|((m-n:ℤ):ℝ)|)) ≤
        (4*p.toReal+1)*‖a‖*h^(-(1/p.toReal)) := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  let b := shift n (appendixDReciprocalEnvelope hp hh)
  let u : Coeff 1 := holderProduct (q := 1) a b
  have he (m : ℤ) : ‖u m‖ = ‖a m‖/(h+|((m-n:ℤ):ℝ)|) := by
    simp only [u,holderProduct_apply,norm_mul,b,shift_apply,
      norm_appendixDReciprocalEnvelope_apply,div_eq_mul_inv]
  have hs : Summable (fun m : ℤ => ‖u m‖) := by
    simpa only [ENNReal.toReal_one,Real.rpow_one] using u.property.summable (by norm_num)
  refine ⟨by simpa only [he] using hs,?_⟩
  have hn : ‖b‖ ≤ (4*p.toReal+1)*h^(-(1/p.toReal)) := by
    dsimp only [b]
    rw [norm_shift]
    exact norm_appendixDReciprocalEnvelope_le hp hh _ (fun k => by
      rw [norm_appendixDReciprocalEnvelope_apply])
  have hu : (∑' m : ℤ, ‖u m‖) = ‖u‖ := by
    simpa only [ENNReal.toReal_one,Real.rpow_one] using
      (lp.norm_rpow_eq_tsum (by norm_num : 0 < (1:ℝ≥0∞).toReal) u).symm
  calc
    _ = ‖u‖ := by simpa only [he] using hu
    _ ≤ ‖a‖*‖b‖ := norm_holderProduct_le a b
    _ ≤ ‖a‖*((4*p.toReal+1)*h^(-(1/p.toReal))) :=
      mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = _ := by ring

/-- The actual scalar sum splits into a distant kernel and the coefficient tail. -/
theorem appendixDReciprocalSum_far_near (hp : p ≠ ⊤) (a : Coeff p)
    (n : ℤ) {y : ℝ} (hy : 0 ≤ y) :
    (∑' m : ℤ, ‖a m‖/(1+y+|((m-n:ℤ):ℝ)|)) ≤
      (4*p.toReal+1)*
        (2*‖a‖*(1+y+(n.natAbs:ℝ)/2)^(-(1/p.toReal)) +
          ‖fourierTail (n.natAbs/2+1) a‖*(1+y)^(-(1/p.toReal))) := by
  let t := fourierTail (n.natAbs/2+1) a
  have hn0 : 0 ≤ (n.natAbs:ℝ) := by positivity
  have hh : 1 ≤ 1+y+(n.natAbs:ℝ)/2 := by linarith
  have hg : 1 ≤ 1+y := by linarith
  have hfull := appendixDReciprocalSum_height_bound hp hg a n
  have hfar := appendixDReciprocalSum_height_bound hp hh a n
  have hnear := appendixDReciprocalSum_height_bound hp hg t n
  have hpoint (m : ℤ) : ‖a m‖/(1+y+|((m-n:ℤ):ℝ)|) ≤
      2*(‖a m‖/(1+y+(n.natAbs:ℝ)/2+|((m-n:ℤ):ℝ)|)) +
        ‖t m‖/(1+y+|((m-n:ℤ):ℝ)|) := by
    by_cases hdist : n.natAbs ≤ 2*(m-n).natAbs
    · have hd : (n.natAbs:ℝ)/2 ≤ |((m-n:ℤ):ℝ)| := by
        have hc : (n.natAbs:ℝ) ≤ 2*((m-n).natAbs:ℝ) := by exact_mod_cast hdist
        simpa only [Nat.cast_natAbs,Int.cast_abs] using (show (n.natAbs:ℝ)/2 ≤ ((m-n).natAbs:ℝ) by linarith)
      have hb : ‖a m‖/(1+y+|((m-n:ℤ):ℝ)|) ≤
          2*(‖a m‖/(1+y+(n.natAbs:ℝ)/2+|((m-n:ℤ):ℝ)|)) := by
        rw [← mul_div_assoc]
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith [mul_nonneg (norm_nonneg (a m))
          (show 0 ≤ 1+y+|((m-n:ℤ):ℝ)|-(n.natAbs:ℝ)/2 by linarith)]
      exact hb.trans (le_add_of_nonneg_right (by positivity))
    · have ht : n.natAbs/2+1 ≤ m.natAbs := by
        have htri : n.natAbs ≤ (m-n).natAbs+m.natAbs := by
          simpa only [sub_sub_cancel,add_comm] using Int.natAbs_sub_le m (m-n)
        omega
      have he : t m = a m := by simp only [t,fourierTail_apply,if_pos ht]
      rw [he]
      exact le_add_of_nonneg_left (by positivity)
  have hs := (hfar.1.mul_left 2).add hnear.1
  have hb := hfull.1.tsum_le_tsum hpoint hs
  rw [(hfar.1.mul_left 2).tsum_add hnear.1,tsum_mul_left] at hb
  calc
    _ ≤ 2*(∑' m : ℤ, ‖a m‖/(1+y+(n.natAbs:ℝ)/2+|((m-n:ℤ):ℝ)|)) +
        (∑' m : ℤ, ‖t m‖/(1+y+|((m-n:ℤ):ℝ)|)) := hb
    _ ≤ 2*((4*p.toReal+1)*‖a‖*(1+y+(n.natAbs:ℝ)/2)^(-(1/p.toReal))) +
        (4*p.toReal+1)*‖t‖*(1+y)^(-(1/p.toReal)) :=
      add_le_add (mul_le_mul_of_nonneg_left hfar.2 (by norm_num)) hnear.2
    _ = _ := by ring

/-- The two source denominators with the corrected half-radius tail and an explicit constant. -/
theorem appendixDReciprocalSum_source_bound (hp : p ≠ ⊤) (a : Coeff p)
    (n : ℤ) {y : ℝ} (hy : 0 ≤ y) :
    (∑' m : ℤ, ‖a m‖/(1+y+|((m-n:ℤ):ℝ)|)) ≤
      (8*(4*p.toReal+1))*
        (‖a‖/(1+(n.natAbs:ℝ)^(1/p.toReal)+y^(1/p.toReal)) +
          ‖fourierTail (n.natAbs/2+1) a‖/(1+y^(1/p.toReal))) := by
  let r := 1/p.toReal
  let x : ℝ := n.natAbs
  let H := 1+y+x/2
  let J := 1+y
  let D := 1+x^r+y^r
  let E := 1+y^r
  let t := ‖fourierTail (n.natAbs/2+1) a‖
  have hp1 : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hp (show 1 ≤ p from Fact.out)
  have hp0 : 0 < p.toReal := zero_lt_one.trans_le hp1
  have hr : 0 < r := one_div_pos.mpr hp0
  have hr1 : r ≤ 1 := (div_le_one hp0).mpr hp1
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hH : 1 ≤ H := by dsimp [H]; linarith
  have hJ : 1 ≤ J := by dsimp [J]; linarith
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hJ0 : 0 < J := zero_lt_one.trans_le hJ
  have hHr : 0 < H^r := Real.rpow_pos_of_pos hH0 _
  have hJr : 0 < J^r := Real.rpow_pos_of_pos hJ0 _
  have hD0 : 0 < D := by dsimp [D]; positivity
  have hE0 : 0 < E := by dsimp [E]; positivity
  have hD : D ≤ 4*H^r := by
    have hxH : x^r ≤ 2*H^r := by
      calc
        _ ≤ (2*H)^r := Real.rpow_le_rpow hx (by dsimp [H]; linarith) hr.le
        _ = (2:ℝ)^r*H^r := Real.mul_rpow (by norm_num) hH0.le
        _ ≤ 2*H^r := mul_le_mul_of_nonneg_right
          (by simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hr1) hHr.le
    have hyH : y^r ≤ H^r := Real.rpow_le_rpow hy (by dsimp [H]; linarith) hr.le
    have h1 : 1 ≤ H^r := Real.one_le_rpow hH hr.le
    dsimp [D]
    linarith
  have hE : E ≤ 2*J^r := by
    have hyJ : y^r ≤ J^r := Real.rpow_le_rpow hy (by dsimp [J]; linarith) hr.le
    have h1 : 1 ≤ J^r := Real.one_le_rpow hJ hr.le
    dsimp [E]
    linarith
  have hleft : 2*‖a‖/H^r ≤ 8*‖a‖/D := by
    apply (div_le_div_iff₀ hHr hD0).mpr
    nlinarith [mul_nonneg (norm_nonneg a) (sub_nonneg.mpr hD)]
  have hright : t/J^r ≤ 8*t/E := by
    have ht : 0 ≤ t := norm_nonneg _
    apply (div_le_div_iff₀ hJr hE0).mpr
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hE),mul_nonneg ht hJr.le]
  have hb := appendixDReciprocalSum_far_near hp a n hy
  change (∑' m : ℤ, ‖a m‖/(1+y+|((m-n:ℤ):ℝ)|)) ≤
    (4*p.toReal+1)*(2*‖a‖*H^(-r)+t*J^(-r)) at hb
  rw [Real.rpow_neg hH0.le,Real.rpow_neg hJ0.le,← div_eq_mul_inv,← div_eq_mul_inv] at hb
  apply hb.trans
  change (4*p.toReal+1)*(2*‖a‖/H^r+t/J^r) ≤
    (8*(4*p.toReal+1))*(‖a‖/D+t/E)
  calc
    _ ≤ (4*p.toReal+1)*(8*‖a‖/D+8*t/E) :=
      mul_le_mul_of_nonneg_left (add_le_add hleft hright) (by positivity)
    _ = _ := by ring

end NLS.Coeff
