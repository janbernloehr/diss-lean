import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! # The real gap arcsine kernel and integration by parts with zero endpoint data. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open MeasureTheory intervalIntegral
namespace NLS.ComplexAnalysis

theorem hasDerivAt_gap_arcsin (a b x : ℝ) (hab : a < b) (hx : x ∈ Ioo a b) :
    HasDerivAt (fun y => Real.arcsin ((2*y-a-b)/(b-a)))
      (Real.sqrt ((x-a)*(b-x)))⁻¹ x := by
  let t := (2*x-a-b)/(b-a)
  have hg : 0 < b-a := sub_pos.mpr hab
  have hprod : 0 < (x-a)*(b-x) := mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
  have ht : t ∈ Ioo (-1) 1 := by
    dsimp only [t]
    constructor
    · apply (lt_div_iff₀ hg).mpr
      linarith [hx.1]
    · apply (div_lt_iff₀ hg).mpr
      linarith [hx.2]
  have hs : Real.sqrt (1-t^2) = 2*Real.sqrt ((x-a)*(b-x))/(b-a) := by
    have he : 1-t^2 = 4*((x-a)*(b-x))/(b-a)^2 := by
      dsimp only [t]
      field_simp [ne_of_gt hg]
      ring
    rw [he,Real.sqrt_div (by linarith : 0 ≤ 4*((x-a)*(b-x))),Real.sqrt_sq_eq_abs,abs_of_pos hg,Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have htder : HasDerivAt (fun y : ℝ => (2*y-a-b)/(b-a)) (2/(b-a)) x := by
    convert! ((((hasDerivAt_id x).const_mul 2).sub_const a).sub_const b).div_const (b-a) using 1
    ring
  have h := (Real.hasDerivAt_arcsin (ne_of_gt ht.1) (ne_of_lt ht.2)).comp x htder
  rw [hs] at h
  convert! h using 1
  have hsne : Real.sqrt ((x-a)*(b-x)) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2))).ne'
  field_simp [hsne,ne_of_gt hg]

theorem intervalIntegrable_gap_arcsine_kernel (a b : ℝ) (hab : a < b) :
    IntervalIntegrable (fun x => (Real.sqrt ((x-a)*(b-x)))⁻¹) volume a b := by
  rw [intervalIntegrable_iff,Set.uIoc_of_le hab.le]
  apply integrableOn_deriv_of_nonneg
    (g' := fun x => (Real.sqrt ((x-a)*(b-x)))⁻¹)
    (g := fun x => Real.arcsin ((2*x-a-b)/(b-a)))
  · exact (Real.continuous_arcsin.comp (by fun_prop)).continuousOn
  · intro x hx
    exact hasDerivAt_gap_arcsin a b x hab hx
  · intro x hx
    positivity

theorem integral_gap_arcsine_kernel (a b : ℝ) (hab : a < b) :
    (∫ x in a..b, (Real.sqrt ((x-a)*(b-x)))⁻¹) = Real.pi := by
  have h := integral_eq_sub_of_hasDerivAt_of_le hab.le
    (f := fun x => Real.arcsin ((2*x-a-b)/(b-a)))
    (f' := fun x => (Real.sqrt ((x-a)*(b-x)))⁻¹)
    (Real.continuous_arcsin.comp (by fun_prop)).continuousOn
    (fun x hx => hasDerivAt_gap_arcsin a b x hab hx) (intervalIntegrable_gap_arcsine_kernel a b hab)
  have ha : (2*a-a-b)/(b-a) = -1 := by
    rw [show 2*a-a-b = -(b-a) by ring,neg_div,div_self (sub_ne_zero.mpr hab.ne')]
  have hb : (2*b-a-b)/(b-a) = 1 := by
    rw [show 2*b-a-b = b-a by ring,div_self (sub_ne_zero.mpr hab.ne')]
  rw [ha,hb,Real.arcsin_neg_one,Real.arcsin_one] at h
  linarith

theorem integral_eq_weighted_deriv_of_zero_endpoints
    (f f' : ℝ → ℝ) (a b c : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hfa : f a = 0) (hfb : f b = 0)
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hint : IntervalIntegrable f' volume a b) :
    (∫ x in a..b, f x) = ∫ x in a..b, (c-x)*f' x := by
  have hfi : IntervalIntegrable f volume a b := hf.intervalIntegrable_of_Icc hab
  have hwi : IntervalIntegrable (fun x => (c-x)*f' x) volume a b :=
    hint.continuousOn_mul (by fun_prop)
  have hg : ContinuousOn (fun x => (c-x)*f x) (Icc a b) :=
    (continuousOn_const.sub continuousOn_id).mul hf
  have hgd (x : ℝ) (hx : x ∈ Ioo a b) :
      HasDerivAt (fun y => (c-y)*f y) (-f x+(c-x)*f' x) x := by
    convert! ((hasDerivAt_id x).const_sub c).mul (hderiv x hx) using 1
    simp only [id_eq]
    ring
  have he := integral_eq_sub_of_hasDerivAt_of_le hab hg hgd (hfi.neg.add hwi)
  rw [hfa,hfb,mul_zero,mul_zero,sub_self] at he
  have hs : (∫ y in a..b, -f y+(c-y)*f' y) = (∫ y in a..b, -f y)+(∫ y in a..b, (c-y)*f' y) := by
    simpa only [Pi.neg_apply,Pi.add_apply] using intervalIntegral.integral_add hfi.neg hwi
  rw [hs,intervalIntegral.integral_neg] at he
  linarith



end NLS.ComplexAnalysis
