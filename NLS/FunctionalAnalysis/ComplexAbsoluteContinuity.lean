import NLS.FunctionalAnalysis.IntegralAbsoluteContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Complex absolute continuity and the fundamental theorem

Real and imaginary projections reduce almost-everywhere differentiability to
mathlib's real-valued theorem. The vector-valued primitive then gives the
fundamental theorem and integration by parts for complex functions.
-/

noncomputable section
open MeasureTheory Set Filter
namespace NLS.FunctionalAnalysis

/-- Bounded linear maps preserve absolute continuity. -/
theorem absolutelyContinuousOnInterval_clm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → E} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (L : E →L[ℝ] F) :
    AbsolutelyContinuousOnInterval (fun x => L (f x)) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  have hpos : 0 < ‖L‖ + 1 := by positivity
  obtain ⟨δ, hδ, hδprop⟩ := hf (ε / (‖L‖ + 1)) (div_pos hε hpos)
  refine ⟨δ, hδ, fun intervals hi hl => ?_⟩
  calc
    (∑ i ∈ Finset.range intervals.1, dist (L (f (intervals.2 i).1)) (L (f (intervals.2 i).2))) ≤
        ‖L‖ * ∑ i ∈ Finset.range intervals.1, dist (f (intervals.2 i).1) (f (intervals.2 i).2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => L.lipschitz.dist_le_mul _ _)
    _ ≤ (‖L‖ + 1) * ∑ i ∈ Finset.range intervals.1,
        dist (f (intervals.2 i).1) (f (intervals.2 i).2) :=
      mul_le_mul_of_nonneg_right (by linarith) (Finset.sum_nonneg (fun _ _ => dist_nonneg))
    _ < (‖L‖ + 1) * (ε / (‖L‖ + 1)) := mul_lt_mul_of_pos_left (hδprop intervals hi hl) hpos
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hpos)

/-- A complex absolutely continuous function is differentiable almost everywhere. -/
theorem ae_differentiableAt_complex {f : ℝ → ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∀ᵐ x : ℝ, x ∈ uIcc a b → DifferentiableAt ℝ f x := by
  have hre := (absolutelyContinuousOnInterval_clm hf Complex.reCLM).ae_differentiableAt
  have him := (absolutelyContinuousOnInterval_clm hf Complex.imCLM).ae_differentiableAt
  filter_upwards [hre, him] with x hr hi
  intro hx
  have hd := (hr hx).hasDerivAt.ofReal_comp.add
    ((hi hx).hasDerivAt.ofReal_comp.mul_const Complex.I)
  have he : (fun t : ℝ => ((f t).re : ℂ) + ((f t).im : ℂ) * Complex.I) = f := by
    funext t
    exact Complex.re_add_im (f t)
  simpa only [Complex.reCLM_apply, Complex.imCLM_apply, Pi.add_def, he] using hd.differentiableAt

/-- The vector-valued fundamental theorem with a specified almost-everywhere derivative. -/
theorem integral_eq_sub_of_ac_of_ae_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f g : ℝ → E} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : IntervalIntegrable g volume a b)
    (hfg : ∀ᵐ x : ℝ, x ∈ uIcc a b → HasDerivAt f (g x) x) :
    (∫ t in a..b, g t) = f b - f a := by
  have hi := absolutelyContinuousOnInterval_integral hg (c := a) (by simp)
  have hz : ∀ᵐ x : ℝ, x ∈ uIcc a b →
      HasDerivAt (fun t => f t - ∫ u in a..t, g u) 0 x := by
    filter_upwards [hfg, hg.ae_hasDerivAt_integral] with x hx hi
    intro hxi
    simpa only [Pi.sub_def, sub_self] using (hx hxi).sub (hi hxi a (by simp))
  obtain ⟨c, hc⟩ := (hf.sub hi).const_of_ae_hasDerivAt_zero hz
  have ha := hc a (by simp)
  have hb := hc b (by simp)
  simp only [Pi.sub_apply, intervalIntegral.integral_same, sub_zero] at ha
  change f b - ∫ t in a..b, g t = c at hb
  rw [← ha] at hb
  rw [← hb]
  abel

/-- The fundamental theorem for the actual derivative of a complex AC function. -/
theorem integral_deriv_eq_sub_complex {f : ℝ → ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hfi : IntervalIntegrable (deriv f) volume a b) :
    (∫ t in a..b, deriv f t) = f b - f a := by
  apply integral_eq_sub_of_ac_of_ae_hasDerivAt hf hfi
  filter_upwards [ae_differentiableAt_complex hf] with x hx
  intro hxi
  exact (hx hxi).hasDerivAt

/-- Integration by parts for complex absolutely continuous factors. -/
theorem integral_mul_deriv_eq_complex {f g : ℝ → ℂ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : AbsolutelyContinuousOnInterval g a b)
    (hfi : IntervalIntegrable (deriv f) volume a b)
    (hgi : IntervalIntegrable (deriv g) volume a b) :
    (∫ t in a..b, f t * deriv g t) = f b * g b - f a * g a - ∫ t in a..b, deriv f t * g t := by
  have hfg : AbsolutelyContinuousOnInterval (fun t => f t * g t) a b := by
    simpa only [Pi.smul_def, smul_eq_mul, Pi.mul_def] using hf.smul hg
  have hint := (hfi.mul_continuousOn hg.continuousOn).add
    (hgi.continuousOn_mul hf.continuousOn)
  have hder : ∀ᵐ x : ℝ, x ∈ uIcc a b →
      HasDerivAt (fun t => f t * g t) (deriv f x * g x + f x * deriv g x) x := by
    filter_upwards [ae_differentiableAt_complex hf, ae_differentiableAt_complex hg] with x hx hy
    intro hxi
    exact (hx hxi).hasDerivAt.mul (hy hxi).hasDerivAt
  have h := integral_eq_sub_of_ac_of_ae_hasDerivAt hfg hint hder
  rw [intervalIntegral.integral_add (hfi.mul_continuousOn hg.continuousOn)
    (hgi.continuousOn_mul hf.continuousOn)] at h
  linear_combination h

end NLS.FunctionalAnalysis
