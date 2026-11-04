import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal

namespace NLS.ComplexAnalysis



theorem scalar_sine_duhamel (q u v : ℝ → ℂ) (z : ℂ) (hz : z ≠ 0) (t : ℝ) (ht : 0 ≤ t)
    (hq : Continuous q) (hu : Continuous u) (hv : Continuous v)
    (hdu : ∀ s ∈ Icc 0 t, HasDerivAt u (v s) s)
    (hdv : ∀ s ∈ Icc 0 t, HasDerivAt v ((q s-z^2)*u s) s) :
    u t = cos (z*t)*u 0 + sin (z*t)/z*v 0 +
      ∫ s in (0 : ℝ)..t, sin (z*((t-s : ℝ) : ℂ))/z*q s*u s := by
  let F : ℝ → ℂ := fun s => cos (z*((t-s : ℝ) : ℂ))*u s +
    sin (z*((t-s : ℝ) : ℂ))/z*v s
  have hphase (s : ℝ) : HasDerivAt (fun r : ℝ => z*((t-r : ℝ) : ℂ)) (-z) s := by
    convert! (((hasDerivAt_id s).const_sub t).ofReal_comp).const_mul z using 1
    simp only [ofReal_neg,ofReal_one,mul_neg_one]
  have hF (s : ℝ) (hs : s ∈ Icc 0 t) : HasDerivAt F
      (sin (z*((t-s : ℝ) : ℂ))/z*q s*u s) s := by
    have hcos := (Complex.hasDerivAt_cos (z*((t-s : ℝ) : ℂ))).scomp s (hphase s)
    have hsin := (Complex.hasDerivAt_sin (z*((t-s : ℝ) : ℂ))).scomp s (hphase s)
    convert! (hcos.mul (hdu s hs)).add ((hsin.div_const z).mul (hdv s hs)) using 1
    dsimp only [Function.comp_def]
    field_simp
    ring
  have hcont : Continuous F := by dsimp only [F];fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hcont.continuousOn
    (fun s hs => hF s ⟨hs.1.le,hs.2.le⟩)
    ((show Continuous (fun s : ℝ => sin (z*((t-s : ℝ) : ℂ))/z*q s*u s) by fun_prop).intervalIntegrable 0 t)
  change (∫ s in (0 : ℝ)..t,sin (z*((t-s : ℝ) : ℂ))/z*q s*u s) = F t-F 0 at hint
  rw [hint]
  dsimp only [F]
  simp only [sub_self,ofReal_zero,mul_zero,cos_zero,sin_zero,zero_div,one_mul,zero_mul,add_zero,sub_zero]
  ring

theorem scalar_cosine_duhamel (q u v : ℝ → ℂ) (z : ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hq : Continuous q) (hu : Continuous u) (hv : Continuous v)
    (hdu : ∀ s ∈ Icc 0 t, HasDerivAt u (v s) s)
    (hdv : ∀ s ∈ Icc 0 t, HasDerivAt v ((q s-z^2)*u s) s) :
    v t = -z*sin (z*t)*u 0 + cos (z*t)*v 0 +
      ∫ s in (0 : ℝ)..t, cos (z*((t-s : ℝ) : ℂ))*q s*u s := by
  let F : ℝ → ℂ := fun s => -z*sin (z*((t-s : ℝ) : ℂ))*u s +
    cos (z*((t-s : ℝ) : ℂ))*v s
  have hphase (s : ℝ) : HasDerivAt (fun r : ℝ => z*((t-r : ℝ) : ℂ)) (-z) s := by
    convert! (((hasDerivAt_id s).const_sub t).ofReal_comp).const_mul z using 1
    simp only [ofReal_neg,ofReal_one,mul_neg_one]
  have hF (s : ℝ) (hs : s ∈ Icc 0 t) : HasDerivAt F
      (cos (z*((t-s : ℝ) : ℂ))*q s*u s) s := by
    have hcos := (Complex.hasDerivAt_cos (z*((t-s : ℝ) : ℂ))).scomp s (hphase s)
    have hsin := (Complex.hasDerivAt_sin (z*((t-s : ℝ) : ℂ))).scomp s (hphase s)
    convert! (((hsin.const_mul (-z)).mul (hdu s hs)).add (hcos.mul (hdv s hs))) using 1
    dsimp only [Function.comp_def]
    ring
  have hcont : Continuous F := by dsimp only [F];fun_prop
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hcont.continuousOn
    (fun s hs => hF s ⟨hs.1.le,hs.2.le⟩)
    ((show Continuous (fun s : ℝ => cos (z*((t-s : ℝ) : ℂ))*q s*u s) by fun_prop).intervalIntegrable 0 t)
  change (∫ s in (0 : ℝ)..t,cos (z*((t-s : ℝ) : ℂ))*q s*u s) = F t-F 0 at hint
  rw [hint]
  dsimp only [F]
  simp only [sub_self,ofReal_zero,mul_zero,cos_zero,sin_zero,one_mul,zero_mul,zero_add,sub_zero]
  ring

end NLS.ComplexAnalysis
