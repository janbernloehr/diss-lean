import NLS.KdV.HillHminusOneTraceControl
import NLS.KdV.HillHminusOneSourcePrimitive
import NLS.KdV.ClassicalHillHighPrimitiveStrip
import NLS.ComplexAnalysis.LogarithmStripNormalization

/-! # The free logarithmic strip for actual high H^-1 Hill primitives

The positive real part of the source trace prevents either imaginary
strip boundary from being crossed. The free anchor fixes the integer
logarithm ambiguity on all admissible high-disc points in one complex
H^-1 neighborhood, before the spectral index is chosen.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

private theorem real_part_cosh (z : ℂ) : (cosh z).re = Real.cosh z.re * Real.cos z.im := by
  rw [← re_add_im z,cosh_add,cosh_mul_I,sinh_mul_I]
  simp only [← ofReal_cosh,← ofReal_sinh,← ofReal_cos,← ofReal_sin,
    add_re,add_im,mul_re,mul_im,ofReal_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
    sub_zero,add_zero,zero_add,mul_one]

/-- A fixed source trace half-plane confines the actual shifted
primitive to its free imaginary strip on the whole source path. -/
theorem hillHminusShiftedPrimitive_im_strip_of_trace_phase
    (q : PeriodOneHminusOne) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4))
    (ht : (z^2,q) ∈ hillHminusContinuationDomain)
    (hphase : ∀ s ∈ Icc (0 : ℝ) 1,
      0 < ((-1 : ℂ)^n*hillHminusDiscriminant ((s : ℂ) • q) (z^2)).re) :
    |(hillHminusContinuedPrimitive (z^2,q)+I*(n : ℂ)*Real.pi).im| < Real.pi/2 := by
  let F : ℝ → ℂ := fun s => hillHminusContinuedPrimitive (z^2,(s : ℂ) • q)+I*(n : ℂ)*Real.pi
  let f : ℝ → ℝ := fun s => (F s).im
  have hpath (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (z^2,(s : ℂ) • q) ∈ hillHminusContinuationDomain := by
    simpa only [hillHminusContinuationDomain,sourceSegmentMap,zero_add,sub_zero] using
      hillHminusSourceFamily.continuationDomain_segment (z^2,q) ht s hs
  have hc : ContinuousOn f (Icc (0 : ℝ) 1) := by
    exact continuous_im.continuousOn.comp
      ((analyticOnNhd_hillHminusContinuedPrimitive.continuousOn.comp (by fun_prop) hpath).add
        continuous_const.continuousOn) (fun _ _ => mem_univ _)
  have hpos (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : 0 < (cosh (F s)).re := by
    have he : 2*cosh (F s) = (-1 : ℂ)^n*hillHminusDiscriminant ((s : ℂ) • q) (z^2) := by
      dsimp only [F]
      rw [cosh_add_hill_index]
      calc
        _ = (-1 : ℂ)^n*(2*cosh (hillHminusContinuedPrimitive (z^2,(s : ℂ) • q))) := by ring
        _ = _ := by rw [(hillHminusContinuedPrimitive_trace _ (hpath s hs)).1]
    have h := congrArg Complex.re he
    have htwo : (2*cosh (F s)).re = 2*(cosh (F s)).re := by simp
    rw [htwo] at h
    linarith [hphase s hs]
  have hne (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : f s ≠ Real.pi/2 ∧ f s ≠ -Real.pi/2 := by
    have h := hpos s hs
    rw [real_part_cosh] at h
    change 0 < Real.cosh (F s).re*Real.cos (f s) at h
    constructor
    · intro he
      rw [he,Real.cos_pi_div_two,mul_zero] at h
      exact lt_irrefl _ h
    · intro he
      rw [he,show -Real.pi/2 = -(Real.pi/2) by ring,Real.cos_neg,Real.cos_pi_div_two,mul_zero] at h
      exact lt_irrefl _ h
  have h0eq : f 0 = -(z.re-Real.pi*n) := by
    dsimp only [f,F]
    rw [ofReal_zero,zero_smul ℂ q,hillHminusContinuedPrimitive_base,
      show -I*Complex.sqrt (z^2) = -I*z from
        classicalHillFreePrimitive_sq_of_re_pos z (re_pos_of_high_closedBall n hn z hz)]
    simp only [add_im,mul_im,mul_re,neg_re,neg_im,I_re,I_im,natCast_re,natCast_im,
      ofReal_re,ofReal_im,mul_zero,zero_mul,sub_zero,one_mul,neg_zero]
    ring
  have hb : |z.re-Real.pi*n| ≤ Real.pi/4 := by
    have hnorm : ‖z-(Real.pi : ℂ)*n‖ ≤ Real.pi/4 := by
      simpa only [mem_closedBall,dist_eq_norm] using hz
    simpa only [sub_re,mul_re,ofReal_re,ofReal_im,natCast_re,natCast_im,
      mul_zero,zero_mul,sub_zero] using (abs_re_le_norm _).trans hnorm
  have h0 : -Real.pi/2 < f 0 ∧ f 0 < Real.pi/2 := by
    rw [h0eq]
    have hb' := abs_le.mp hb
    constructor <;> linarith [Real.pi_pos]
  have h1 := real_mem_Ioo_of_preconnected_avoids f (Icc (0 : ℝ) 1)
    isPreconnected_Icc hc (-Real.pi/2) (Real.pi/2)
    (fun s hs => ⟨(hne s hs).2,(hne s hs).1⟩) 0 (by constructor <;> norm_num) h0 1
    (by constructor <;> norm_num)
  have hstrip : |f 1| < Real.pi/2 := abs_lt.mpr ⟨by linarith [h1.1],h1.2⟩
  simpa only [f,F,ofReal_one,one_smul] using hstrip

/-- The strip and cutoff are uniform on a complex potential neighborhood,
before all high discs and all points in the actual continuation domain. -/
theorem exists_hillHminus_high_primitive_strip (q : PeriodOneHminusOne) :
    ∃ N : ℕ, ∃ V : Set (PeriodOneHminusOne), 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ a ∈ V, ∀ n : ℕ, N ≤ n → ∀ z ∈ closedBall ((Real.pi : ℂ)*n) (Real.pi/4),
        (z^2,a) ∈ hillHminusContinuationDomain →
          |(hillHminusContinuedPrimitive (z^2,a)+I*(n : ℂ)*Real.pi).im| < Real.pi/2 := by
  obtain ⟨N,V,hN,hV,hq,hphase⟩ := exists_hillHminus_source_high_trace_phase q
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro a ha n hn z hz ht
  exact hillHminusShiftedPrimitive_im_strip_of_trace_phase a n (by omega) z hz ht
    (fun s hs => hphase a ha s hs n hn z hz)

end NLS.KdV
