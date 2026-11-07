import NLS.KdV.HillActionAmplitudeDomain
import NLS.ComplexAnalysis.PrincipalSquareRootSheet
import Mathlib.Analysis.Complex.SqrtDeriv

/-! The actual normalized action amplitude with its positive real
principal branch. ONE common native domain precedes ALL n, and the
amplitude has its exact square and locally uniform inverse-square-root
index bound. No gap or action is divided by. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped Classical
namespace NLS.KdV

def hillHminusActionRatioSqrt (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  Complex.sqrt (hillHminusCanonicalActionRatio n q)

def hillHminusCanonicalActionAmplitude (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  hillHminusActionRatioSqrt n q/((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ)

theorem analyticOnNhd_hillHminusActionRatioSqrt (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusActionRatioSqrt n) hillHminusActionAmplitudeDomain := by
  intro q hq
  have hs : hillHminusCanonicalActionRatio n q ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (hillHminusActionRatio_re_pos_on_amplitude_domain n q hq))
  exact (Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds hs)).comp
    (analyticOnNhd_hillHminusCanonicalActionRatio n q (hillHminusActionAmplitudeDomain_subset_ratio hq))

theorem hillHminusActionRatioSqrt_sq (n : ℕ+) (q : PeriodOneHminusOne) :
    (hillHminusActionRatioSqrt n q)^2 = hillHminusCanonicalActionRatio n q :=
  complex_sqrt_sq _

theorem hillHminusActionRatioSqrt_real_positive (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    (hillHminusActionRatioSqrt n q).im = 0 ∧ 0 < (hillHminusActionRatioSqrt n q).re := by
  obtain ⟨hi,hp⟩ := hillHminusCanonicalActionRatio_real_positive n q hr
  let R := hillHminusCanonicalActionRatio n q
  have hRi : R.im = 0 := hi
  have hR : (R.re:ℂ) = R := by
    simpa only [hRi,Complex.ofReal_zero,zero_mul,add_zero] using Complex.re_add_im R
  have hs : ((Real.sqrt R.re:ℂ))^2 = R := by
    rw [← Complex.ofReal_pow,Real.sq_sqrt hp.le]
    exact hR
  have hsp : 0 < Real.sqrt R.re := Real.sqrt_pos.mpr hp
  have he := eq_principalSqrt_of_sq_of_re_pos (Real.sqrt R.re:ℂ) R hs (by simpa only [Complex.ofReal_re] using hsp)
  change (Complex.sqrt R).im = 0 ∧ 0 < (Complex.sqrt R).re
  rw [← he]
  exact ⟨Complex.ofReal_im _,by simpa only [Complex.ofReal_re] using hsp⟩

theorem hillActionAmplitude_denominator_pos (n : ℕ+) :
    0 < 2*Real.sqrt Real.pi*Real.sqrt (n:ℕ) := by
  have hn : 0 < ((n:ℕ):ℝ) := by exact_mod_cast n.pos
  exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr Real.pi_pos)) (Real.sqrt_pos.mpr hn)

theorem hillActionAmplitude_denominator_sq (n : ℕ+) :
    (((2*Real.sqrt Real.pi*Real.sqrt (n:ℕ):ℝ):ℂ))^2 = 4*((Real.pi:ℂ)*(n:ℕ)) := by
  have hn : 0 ≤ ((n:ℕ):ℝ) := by positivity
  have he : (2*Real.sqrt Real.pi*Real.sqrt (n:ℕ))^2 = 4*(Real.pi*(n:ℕ)) := by
    rw [mul_pow,mul_pow,Real.sq_sqrt Real.pi_pos.le,Real.sq_sqrt hn]
    ring
  exact_mod_cast he

theorem analyticOnNhd_hillHminusCanonicalActionAmplitude (n : ℕ+) :
    AnalyticOnNhd ℂ (hillHminusCanonicalActionAmplitude n) hillHminusActionAmplitudeDomain := by
  intro q hq
  exact (analyticOnNhd_hillHminusActionRatioSqrt n q hq).div_const

theorem hillHminusCanonicalActionAmplitude_sq (n : ℕ+) (q : PeriodOneHminusOne) :
    (hillHminusCanonicalActionAmplitude n q)^2 =
      hillHminusCanonicalActionRatio n q/(4*((Real.pi:ℂ)*(n:ℕ))) := by
  rw [hillHminusCanonicalActionAmplitude,div_pow,hillHminusActionRatioSqrt_sq,hillActionAmplitude_denominator_sq]

theorem hillHminusCanonicalActionAmplitude_real_positive (n : ℕ+) (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) :
    (hillHminusCanonicalActionAmplitude n q).im = 0 ∧ 0 < (hillHminusCanonicalActionAmplitude n q).re := by
  obtain ⟨hi,hp⟩ := hillHminusActionRatioSqrt_real_positive n q hr
  have he : ((hillHminusActionRatioSqrt n q).re:ℂ) = hillHminusActionRatioSqrt n q := by
    simpa only [hi,Complex.ofReal_zero,zero_mul,add_zero] using Complex.re_add_im (hillHminusActionRatioSqrt n q)
  unfold hillHminusCanonicalActionAmplitude
  rw [← he,← Complex.ofReal_div]
  exact ⟨Complex.ofReal_im _,by simpa only [Complex.ofReal_re] using div_pos hp (hillActionAmplitude_denominator_pos n)⟩

theorem hillHminusCanonicalActionAmplitude_ne_zero (n : ℕ+) (q : PeriodOneHminusOne)
    (hq : q ∈ hillHminusActionAmplitudeDomain) : hillHminusCanonicalActionAmplitude n q ≠ 0 := by
  intro he
  have hn := hillHminusCanonicalActionRatio_ne_zero n q (hillHminusActionAmplitudeDomain_subset_ratio hq)
  have hs := hillHminusCanonicalActionAmplitude_sq n q
  rw [he,zero_pow (by decide : (2:ℕ) ≠ 0)] at hs
  exact hn ((div_eq_zero_iff.mp hs.symm).resolve_right (mul_ne_zero (by norm_num)
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) (by exact_mod_cast n.ne_zero))))

end NLS.KdV
