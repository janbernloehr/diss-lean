import NLS.KdV.HillHminusOneRealSpectralExclusion
import NLS.KdV.HillHminusOnePeriodEntries

/-! # Real-band signs on the original rough Hill continuation domain

Actual real Miura charts give trace reality. Nonvanishing along the
original source segment preserves the negative free radicand sign.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ComplexOrder
namespace NLS.KdV

/-- The actual trace is real at every nonnegative energy of every real rough input. -/
theorem hillHminusDiscriminant_im_eq_zero_of_real_nonnegative (q : PeriodOneHminusOne)
    (hq : periodOneHminusConjugation q = q) (x : ℝ) (hx : 0 ≤ x) :
    (hillHminusDiscriminant q (x : ℂ)).im = 0 := by
  obtain ⟨C,hqC,hpos,hc,hr⟩ := exists_real_hillHminusMiuraChart q hq
  let z : ℝ := Real.sqrt (x+C.energyShift.re)
  have hzsq : z^2 = x+C.energyShift.re := Real.sq_sqrt (by linarith)
  have he : (z : ℂ)^2-C.energyShift = (x : ℂ) := by
    apply Complex.ext
    · simpa only [sub_re,← ofReal_pow,ofReal_re] using sub_eq_iff_eq_add.mpr hzsq
    · simp only [sub_im,← ofReal_pow,ofReal_im,hc,sub_self]
  rw [← he,C.trace_shifted_square q hqC]
  exact canonicalDiscriminant_im_eq_zero_of_realType (by simp) (by norm_num)
    _ (periodOnePotential_mem _) (isRealType_periodOnePotential _ (hr q hqC hq).2) z

/-- The original continued domain at a nonnegative real energy has strictly negative actual radicand. -/
theorem hillHminusRadicand_re_neg_of_real_continuation (q : PeriodOneHminusOne)
    (hq : periodOneHminusConjugation q = q) (x : ℝ) (hx : 0 ≤ x)
    (hdom : ((x : ℂ),q) ∈ hillHminusContinuationDomain) :
    (hillHminusRadicand q (x : ℂ)).re < 0 := by
  rw [mem_hillHminusContinuationDomain_iff] at hdom
  have hpath := hdom.2
  let f : ℝ → ℝ := fun r => (hillHminusRadicand ((r : ℂ) • q) (x : ℂ)).re
  have hf : Continuous f := by
    have hg : Continuous (fun r : ℝ => ((x : ℂ),(r : ℂ) • q)) :=
      continuous_const.prodMk (continuous_ofReal.smul continuous_const)
    have hfull : Continuous (fun t : ℂ × PeriodOneHminusOne => hillHminusRadicand t.2 t.1) :=
      analyticOnNhd_hillHminusRadicand_joint.continuous
    have hrad : Continuous (fun r : ℝ => hillHminusRadicand ((r : ℂ) • q) (x : ℂ)) :=
      hfull.comp (f := fun r : ℝ => ((x : ℂ),(r : ℂ) • q)) hg
    exact continuous_re.comp (f := fun r : ℝ => hillHminusRadicand ((r : ℂ) • q) (x : ℂ)) hrad
  have him (r : ℝ) : (hillHminusRadicand ((r : ℂ) • q) (x : ℂ)).im = 0 := by
    have ht := hillHminusDiscriminant_im_eq_zero_of_real_nonnegative ((r : ℂ) • q)
      (periodOneHminusConjugation_real_smul_fixed r q hq) x hx
    simp only [hillHminusRadicand,sub_im,pow_two,mul_im,ht,mul_zero,zero_mul,add_zero]
    norm_num
  have hne (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) : f r ≠ 0 := by
    intro he
    exact hpath r hr (Complex.ext he (him r))
  have hbase : f 0 ≤ 0 := by
    have hsqrt : sqrt (x : ℂ) = (Real.sqrt x : ℂ) := by
      simpa only [ofReal_re] using Complex.sqrt_of_nonneg (by exact_mod_cast hx : (0 : ℂ) ≤ (x : ℂ))
    have he : f 0 = (2*Real.cos (Real.sqrt x))^2-4 := by
      simp only [f,ofReal_zero,zero_smul,hillHminusRadicand,hillHminusDiscriminant_zero,hsqrt]
      norm_num [pow_two,mul_re,mul_im,cos_ofReal_re,cos_ofReal_im]
    rw [he]
    nlinarith [Real.neg_one_le_cos (Real.sqrt x),Real.cos_le_one (Real.sqrt x)]
  have hb : f 0 < 0 := lt_of_le_of_ne hbase (hne 0 ⟨le_rfl,by norm_num⟩)
  have hend : f 1 < 0 := by
    by_contra h
    have hnon : 0 ≤ f 1 := le_of_not_gt h
    obtain ⟨r,hr,he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
      hf.continuousOn ⟨hb.le,hnon⟩
    exact hne r hr he
  simpa only [f,ofReal_one,one_smul] using hend

end NLS.KdV
