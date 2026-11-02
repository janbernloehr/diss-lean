import NLS.KdV.ClassicalHillReality
import NLS.KdV.ClassicalHillConjugation
import NLS.ComplexAnalysis.ContinuousSquareRootPath

/-! # Physical half-plane sheets of the continued Hill primitive

The actual scalar Green identity prevents a continued multiplier from
crossing the unit circle at nonreal energy. Continuity from the free
normalization then fixes the sign of the primitive's real part throughout
each energy half-plane, at every real continuous potential.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.LinearVolterra NLS.ComplexAnalysis
open scoped ComplexConjugate
namespace NLS.KdV

/-- The free primitive has the correct sign in both nonreal half-planes. -/
theorem classicalHillFreePrimitive_re_sign (lambda : ℂ) (him : lambda.im ≠ 0) :
    0 < lambda.im * (classicalHillFreePrimitive lambda).re := by
  have hs : (Complex.sqrt lambda)^2 = lambda := by
    have h := Complex.cpow_nat_inv_pow lambda (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt,one_div] using h
  have hre : 0 ≤ (Complex.sqrt lambda).re := by
    rw [Complex.sqrt,cpow_inv_two_re]
    positivity
  have he : 2*(Complex.sqrt lambda).re*(Complex.sqrt lambda).im = lambda.im := by
    have h := congrArg Complex.im hs
    simp only [pow_two,mul_im] at h
    linear_combination h
  have hrne : (Complex.sqrt lambda).re ≠ 0 := by
    intro h
    apply him
    rw [h,mul_zero,zero_mul] at he
    exact he.symm
  have hine : (Complex.sqrt lambda).im ≠ 0 := by
    intro h
    apply him
    rw [h,mul_zero] at he
    exact he.symm
  have hrpos := lt_of_le_of_ne hre (Ne.symm hrne)
  simp only [classicalHillFreePrimitive,mul_re,neg_re,I_re,I_im,
    zero_mul,neg_mul,one_mul,zero_sub,neg_neg]
  rw [← he]
  nlinarith [sq_pos_of_ne_zero hine]

/-- The free normalization fixes the actual sheet globally: the real
part is positive in the upper energy half-plane and negative in the lower.
There is no smallness assumption on the real continuous potential. -/
theorem classicalHillContinuedPrimitive_re_sign
    (q : Curve ℂ) (hq : ∀ t, (q t).im = 0) (lambda : ℂ) (him : lambda.im ≠ 0) :
    0 < lambda.im * (classicalHillContinuedPrimitive (lambda,q)).re := by
  let f : ℝ → ℝ := fun s => lambda.im *
    (classicalHillContinuedPrimitive (lambda,(s : ℂ) • q)).re
  have hreal (s : ℝ) : ∀ t, (((s : ℂ) • q) t).im = 0 := by
    intro t
    simp only [ContinuousMap.smul_apply,smul_eq_mul,mul_im,ofReal_re,ofReal_im,hq t,
      mul_zero,zero_mul,add_zero]
  have hpath : Continuous (fun s : ℝ => (lambda,(s : ℂ) • q)) := by fun_prop
  have hc : ContinuousOn f (Icc (0 : ℝ) 1) := by
    apply continuous_const.continuousOn.mul
    exact continuous_re.continuousOn.comp
      (analyticOnNhd_classicalHillContinuedPrimitive.continuousOn.comp hpath.continuousOn
        (fun s _ => mem_classicalHillContinuationDomain_of_im_ne_zero _ (hreal s) lambda him))
      (fun _ _ => mem_univ _)
  have hne (s : ℝ) : f s ≠ 0 :=
    mul_ne_zero him (classicalHillContinuedPrimitive_re_ne_zero_off_real _ (hreal s) lambda him)
  have h0 : 0 < f 0 := by
    dsimp only [f]
    rw [ofReal_zero,zero_smul ℂ q,classicalHillContinuedPrimitive_base]
    exact classicalHillFreePrimitive_re_sign lambda him
  have h1 : 0 < f 1 := by
    by_contra hn
    obtain ⟨s,_,hs⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hc
      (show (0 : ℝ) ∈ Icc (f 1) (f 0) from ⟨not_lt.mp hn,h0.le⟩)
    exact hne s hs
  simpa only [f,ofReal_one,one_smul] using h1

theorem classicalHillContinuedPrimitive_re_pos
    (q : Curve ℂ) (hq : ∀ t, (q t).im = 0) (lambda : ℂ) (him : 0 < lambda.im) :
    0 < (classicalHillContinuedPrimitive (lambda,q)).re :=
  (mul_pos_iff_of_pos_left him).mp (classicalHillContinuedPrimitive_re_sign q hq lambda him.ne')

theorem classicalHillContinuedPrimitive_re_neg
    (q : Curve ℂ) (hq : ∀ t, (q t).im = 0) (lambda : ℂ) (him : lambda.im < 0) :
    (classicalHillContinuedPrimitive (lambda,q)).re < 0 := by
  have h := classicalHillContinuedPrimitive_re_sign q hq lambda him.ne
  rcases mul_pos_iff.mp h with h | h
  · exact False.elim (not_lt_of_ge him.le h.1)
  · exact h.2

/-- The constructed actual Floquet multiplier is the expanding one in
the upper energy half-plane. -/
theorem one_lt_norm_classicalHillContinuedMultiplier
    (q : Curve ℂ) (hq : ∀ t, (q t).im = 0) (lambda : ℂ) (him : 0 < lambda.im) :
    1 < ‖classicalHillContinuedMultiplier (lambda,q)‖ := by
  rw [← exp_classicalHillContinuedPrimitive (lambda,q)
    (mem_classicalHillContinuationDomain_of_im_ne_zero q hq lambda him.ne'),norm_exp,
    Real.one_lt_exp_iff]
  exact classicalHillContinuedPrimitive_re_pos q hq lambda him

/-- The same free-normalized multiplier is the contracting one in the
lower energy half-plane. -/
theorem norm_classicalHillContinuedMultiplier_lt_one
    (q : Curve ℂ) (hq : ∀ t, (q t).im = 0) (lambda : ℂ) (him : lambda.im < 0) :
    ‖classicalHillContinuedMultiplier (lambda,q)‖ < 1 := by
  rw [← exp_classicalHillContinuedPrimitive (lambda,q)
    (mem_classicalHillContinuationDomain_of_im_ne_zero q hq lambda him.ne),norm_exp,
    Real.exp_lt_one_iff]
  exact classicalHillContinuedPrimitive_re_neg q hq lambda him

end NLS.KdV
