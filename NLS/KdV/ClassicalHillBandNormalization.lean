import NLS.KdV.ClassicalHillPrimitiveReflection
import NLS.KdV.ClassicalContourCoverage

/-! # Indexed real-band normalization of the actual Hill primitive

At an admissible real energy the continued primitive is imaginary and
its root never vanishes. Consequently it cannot cross an integer multiple
of i*pi along a real source path. The free anchor fixes its band throughout
the entire source path, without a small-potential assumption.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

/-- The free normalization at every nonnegative real frequency. -/
theorem classicalHillFreePrimitive_ofReal_sq (x : ℝ) (hx : 0 ≤ x) :
    classicalHillFreePrimitive ((x : ℂ)^2) = -I*x := by
  have hs : Complex.sqrt ((x : ℂ)^2) = (x : ℂ) := by
    rw [← ofReal_pow,Complex.sqrt_of_nonneg (by exact_mod_cast sq_nonneg x)]
    simp only [ofReal_re,Real.sqrt_sq hx]
  rw [classicalHillFreePrimitive,hs]

/-- Principal energy square root agrees with the frequency throughout
the right half-plane, fixing the free primitive there. -/
theorem classicalHillFreePrimitive_sq_of_re_pos (z : ℂ) (hz : 0 < z.re) :
    classicalHillFreePrimitive (z^2) = -I*z := by
  have hs : (Complex.sqrt (z^2))^2 = z^2 := by
    have h := Complex.cpow_nat_inv_pow (z^2) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  have hre : 0 ≤ (Complex.sqrt (z^2)).re := by
    rw [Complex.sqrt,cpow_inv_two_re]
    positivity
  have he : Complex.sqrt (z^2) = z := by
    rcases eq_or_eq_neg_of_sq_eq_sq _ _ hs with h | h
    · exact h
    · rw [h,neg_re] at hre
      linarith
  rw [classicalHillFreePrimitive,he]

/-- A branch-free real band never contains an integer primitive value. -/
theorem classicalHillContinuedPrimitive_im_ne_int_pi
    (q : Curve ℂ) (hq : ∀ t, (q t).im = 0) (lambda : ℂ) (him : lambda.im = 0)
    (ht : (lambda,q) ∈ classicalHillContinuationDomain) (k : ℤ) :
    (classicalHillContinuedPrimitive (lambda,q)).im ≠ (k : ℝ)*Real.pi := by
  intro he
  have hre := classicalHillContinuedPrimitive_re_eq_zero_of_im_eq_zero q hq lambda him ht
  have hval : classicalHillContinuedPrimitive (lambda,q) =
      (((k : ℝ)*Real.pi : ℝ) : ℂ)*I := by
    apply Complex.ext <;> simp only [mul_re,mul_im,ofReal_re,ofReal_im,I_re,I_im,
      mul_zero,sub_self,mul_one,add_zero]
    · exact hre
    · exact he
  have hsin : sinh (classicalHillContinuedPrimitive (lambda,q)) = 0 := by
    rw [hval,sinh_mul_I,← ofReal_sin,Real.sin_int_mul_pi,ofReal_zero,zero_mul]
  have hr := (classicalHillContinuedPrimitive_trace (lambda,q) ht).2
  rw [hsin,mul_zero] at hr
  exact classicalHillContinuedRoot_ne_zero (lambda,q) ht hr.symm

/-- The imaginary value stays in its free real band on the full
admissible source domain. Both strict band inequalities are retained. -/
theorem classicalHillContinuedPrimitive_im_in_free_band
    (q : Curve ℂ) (hq : ∀ t, (q t).im = 0) (lambda : ℂ) (him : lambda.im = 0)
    (ht : (lambda,q) ∈ classicalHillContinuationDomain) (k : ℤ)
    (hfree : (k : ℝ)*Real.pi < (classicalHillFreePrimitive lambda).im ∧
      (classicalHillFreePrimitive lambda).im < ((k : ℝ)+1)*Real.pi) :
    (k : ℝ)*Real.pi < (classicalHillContinuedPrimitive (lambda,q)).im ∧
      (classicalHillContinuedPrimitive (lambda,q)).im < ((k : ℝ)+1)*Real.pi := by
  let f : ℝ → ℝ := fun s => (classicalHillContinuedPrimitive (lambda,(s : ℂ) • q)).im
  have hpath (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      (lambda,(s : ℂ) • q) ∈ classicalHillContinuationDomain := by
    simpa only [sourceSegmentMap,zero_add,sub_zero] using
      classicalHillContinuationDomain_segment (lambda,q) ht s hs
  have hreal (s : ℝ) : ∀ t, (((s : ℂ) • q) t).im = 0 := by
    intro t
    simp only [ContinuousMap.smul_apply,smul_eq_mul,mul_im,ofReal_re,ofReal_im,hq t,
      mul_zero,zero_mul,add_zero]
  have hc : ContinuousOn f (Icc (0 : ℝ) 1) := by
    exact continuous_im.continuousOn.comp
      (analyticOnNhd_classicalHillContinuedPrimitive.continuousOn.comp (by fun_prop) hpath)
      (fun _ _ => mem_univ _)
  have hne (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (j : ℤ) : f s ≠ (j : ℝ)*Real.pi :=
    classicalHillContinuedPrimitive_im_ne_int_pi _ (hreal s) lambda him (hpath s hs) j
  have h0 : (k : ℝ)*Real.pi < f 0 ∧ f 0 < ((k : ℝ)+1)*Real.pi := by
    dsimp only [f]
    rw [ofReal_zero,zero_smul ℂ q,classicalHillContinuedPrimitive_base]
    exact hfree
  have h1 : (k : ℝ)*Real.pi < f 1 ∧ f 1 < ((k : ℝ)+1)*Real.pi := by
    constructor
    · by_contra hn
      obtain ⟨s,hs,he⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hc
        (show (k : ℝ)*Real.pi ∈ Icc (f 1) (f 0) from ⟨not_lt.mp hn,h0.1.le⟩)
      exact hne s hs k he
    · by_contra hn
      obtain ⟨s,hs,he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc
        (show ((k : ℝ)+1)*Real.pi ∈ Icc (f 0) (f 1) from ⟨h0.2.le,not_lt.mp hn⟩)
      exact hne s hs (k+1) (by simpa only [Int.cast_add,Int.cast_one] using he)
  simpa only [f,ofReal_one,one_smul] using h1

/-- At a nonnegative real frequency between the n-th and (n+1)-st
free centers, the actual primitive has the same indexed imaginary band. -/
theorem classicalHillContinuedPrimitive_ofReal_sq_band
    (q : Curve ℂ) (hq : ∀ t, (q t).im = 0) (x : ℝ) (hx : 0 ≤ x) (n : ℤ)
    (hband : (n : ℝ)*Real.pi < x ∧ x < ((n : ℝ)+1)*Real.pi)
    (ht : ((x : ℂ)^2,q) ∈ classicalHillContinuationDomain) :
    -((n : ℝ)+1)*Real.pi < (classicalHillContinuedPrimitive ((x : ℂ)^2,q)).im ∧
      (classicalHillContinuedPrimitive ((x : ℂ)^2,q)).im < -(n : ℝ)*Real.pi := by
  have hfree : (classicalHillFreePrimitive ((x : ℂ)^2)).im = -x := by
    rw [classicalHillFreePrimitive_ofReal_sq x hx]
    simp
  have him : ((x : ℂ)^2).im = 0 := by simp [pow_two]
  have hb := classicalHillContinuedPrimitive_im_in_free_band q hq ((x : ℂ)^2) him ht (-n-1) (by
    rw [hfree]
    push_cast
    constructor <;> nlinarith [hband.1,hband.2])
  push_cast at hb
  constructor <;> nlinarith [hb.1,hb.2]

end NLS.KdV
