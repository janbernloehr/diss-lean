import NLS.ZakharovShabat.ClassicalTraceHalfPlaneBounds
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Classical trace asymptotics in both half-planes

The real spectral parameter may vary arbitrarily. Only its imaginary part
must tend to the indicated end. The potential is fixed and continuous.
-/

noncomputable section
open Set Complex Filter Topology
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

private theorem tendsto_trace_error_bound {α : Type*} {l : Filter α} {y : α → ℝ}
    (hy : Tendsto y l atTop) (M : ℝ) :
    Tendsto (fun i => 2*M^2/(2*y i) + 2*M^2/(2*y i)^2) l (𝓝 0) := by
  have hd : Tendsto (fun i => 2*y i) l atTop := hy.const_mul_atTop (by norm_num)
  have hd₂ : Tendsto (fun i => (2*y i)^2) l atTop :=
    (tendsto_pow_atTop (by decide : 2 ≠ 0)).comp hd
  simpa only [add_zero] using (hd.const_div_atTop (2*M^2)).add (hd₂.const_div_atTop (2*M^2))

/-- The normalized trace tends to one at the upper end, without a real-part restriction. -/
theorem tendsto_classicalDiscriminant_upper_normalized {α : Type*} {l : Filter α}
    (φ : Curve (ℂ × ℂ)) (z : α → ℂ) (hz : Tendsto (fun i => (z i).im) l atTop) :
    Tendsto (fun i => exp (I*z i) * classicalDiscriminant φ (z i)) l (𝓝 1) := by
  have he : Tendsto (fun i => exp (2*I*z i)) l (𝓝 0) := by
    apply Complex.tendsto_exp_nhds_zero_iff.mpr
    simpa [Complex.mul_re, Function.comp_def] using
      tendsto_neg_atTop_atBot.comp (hz.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have herr : Tendsto (fun i => exp (I*z i) * classicalDiscriminant φ (z i) -
      (1 + exp (2*I*z i))) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
      (tendsto_trace_error_bound hz ‖φ‖)
    filter_upwards [hz.eventually_ge_atTop 1, hz.eventually_ge_atTop (‖φ‖^2)] with i hi hlarge
    exact norm_classicalDiscriminant_upper_sub_free_le φ (z i) (by linarith) hlarge
  simpa only [sub_add_cancel, zero_add, add_zero] using herr.add (he.const_add 1)

/-- The analogous normalization at the lower end. -/
theorem tendsto_classicalDiscriminant_lower_normalized {α : Type*} {l : Filter α}
    (φ : Curve (ℂ × ℂ)) (z : α → ℂ) (hz : Tendsto (fun i => (z i).im) l atBot) :
    Tendsto (fun i => exp (-I*z i) * classicalDiscriminant φ (z i)) l (𝓝 1) := by
  have hy : Tendsto (fun i => -(z i).im) l atTop := tendsto_neg_atBot_atTop.comp hz
  have he : Tendsto (fun i => exp (-2*I*z i)) l (𝓝 0) := by
    apply Complex.tendsto_exp_nhds_zero_iff.mpr
    simpa [Complex.mul_re, Function.comp_def] using hz.const_mul_atBot (by norm_num : (0 : ℝ) < 2)
  have herr : Tendsto (fun i => exp (-I*z i) * classicalDiscriminant φ (z i) -
      (1 + exp (-2*I*z i))) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _
      (show Tendsto (fun i => 2*‖φ‖^2/(-2*(z i).im) +
        2*‖φ‖^2/(-2*(z i).im)^2) l (𝓝 0) by
        simpa only [mul_neg, neg_mul] using tendsto_trace_error_bound hy ‖φ‖)
    filter_upwards [hy.eventually_ge_atTop 1, hy.eventually_ge_atTop (‖φ‖^2)] with i hi hlarge
    exact norm_classicalDiscriminant_lower_sub_free_le φ (z i) (by linarith) hlarge
  simpa only [sub_add_cancel, zero_add, add_zero] using herr.add (he.const_add 1)

/-- Every fixed scalar shift has the same upper free normalization. -/
theorem tendsto_classicalDiscriminant_sub_div_free_upper {α : Type*} {l : Filter α}
    (φ : Curve (ℂ × ℂ)) (z : α → ℂ) (hz : Tendsto (fun i => (z i).im) l atTop) (b : ℂ) :
    Tendsto (fun i => (classicalDiscriminant φ (z i) - b) / (freeDiscriminant (z i) - b))
      l (𝓝 1) := by
  have he : Tendsto (fun i => exp (I*z i)) l (𝓝 0) := by
    apply Complex.tendsto_exp_nhds_zero_iff.mpr
    simpa [Complex.mul_re, Function.comp_def] using tendsto_neg_atTop_atBot.comp hz
  have hn (ψ : Curve (ℂ × ℂ)) :
      Tendsto (fun i => exp (I*z i) * (classicalDiscriminant ψ (z i) - b)) l (𝓝 1) := by
    simpa only [mul_sub, zero_mul, sub_zero] using
      (tendsto_classicalDiscriminant_upper_normalized ψ z hz).sub (he.mul_const b)
  have h := (hn φ).div (hn 0) (by norm_num : (1 : ℂ) ≠ 0)
  change Tendsto (fun i => (exp (I*z i) * (classicalDiscriminant φ (z i) - b)) /
    (exp (I*z i) * (classicalDiscriminant 0 (z i) - b))) l (𝓝 ((1 : ℂ)/1)) at h
  simpa only [Pi.div_apply, classicalDiscriminant_free, mul_div_mul_left _ _ (exp_ne_zero _),
    div_self (by norm_num : (1 : ℂ) ≠ 0)] using! h

/-- Every fixed scalar shift has the same lower free normalization. -/
theorem tendsto_classicalDiscriminant_sub_div_free_lower {α : Type*} {l : Filter α}
    (φ : Curve (ℂ × ℂ)) (z : α → ℂ) (hz : Tendsto (fun i => (z i).im) l atBot) (b : ℂ) :
    Tendsto (fun i => (classicalDiscriminant φ (z i) - b) / (freeDiscriminant (z i) - b))
      l (𝓝 1) := by
  have he : Tendsto (fun i => exp (-I*z i)) l (𝓝 0) := by
    apply Complex.tendsto_exp_nhds_zero_iff.mpr
    simpa [Complex.mul_re, Function.comp_def] using hz
  have hn (ψ : Curve (ℂ × ℂ)) :
      Tendsto (fun i => exp (-I*z i) * (classicalDiscriminant ψ (z i) - b)) l (𝓝 1) := by
    simpa only [mul_sub, zero_mul, sub_zero] using
      (tendsto_classicalDiscriminant_lower_normalized ψ z hz).sub (he.mul_const b)
  have h := (hn φ).div (hn 0) (by norm_num : (1 : ℂ) ≠ 0)
  change Tendsto (fun i => (exp (-I*z i) * (classicalDiscriminant φ (z i) - b)) /
    (exp (-I*z i) * (classicalDiscriminant 0 (z i) - b))) l (𝓝 ((1 : ℂ)/1)) at h
  simpa only [Pi.div_apply, classicalDiscriminant_free, mul_div_mul_left _ _ (exp_ne_zero _),
    div_self (by norm_num : (1 : ℂ) ≠ 0)] using! h

private theorem shifted_ratios_mul (f g : ℂ) :
    ((f-2)/(g-2)) * ((f-(-2))/(g-(-2))) = (f^2-4)/(g^2-4) := by
  rw [div_mul_div_comm]
  congr 1 <;> ring

/-- The full characteristic function also has ratio one to its free value at the upper end. -/
theorem tendsto_classicalDiscriminant_sq_div_free_upper {α : Type*} {l : Filter α}
    (φ : Curve (ℂ × ℂ)) (z : α → ℂ) (hz : Tendsto (fun i => (z i).im) l atTop) :
    Tendsto (fun i => ((classicalDiscriminant φ (z i))^2-4) / ((freeDiscriminant (z i))^2-4))
      l (𝓝 1) := by
  simpa only [Pi.mul_apply, shifted_ratios_mul, mul_one] using!
    (tendsto_classicalDiscriminant_sub_div_free_upper φ z hz 2).mul
      (tendsto_classicalDiscriminant_sub_div_free_upper φ z hz (-2))

/-- The full characteristic function has the corresponding lower-half-plane limit. -/
theorem tendsto_classicalDiscriminant_sq_div_free_lower {α : Type*} {l : Filter α}
    (φ : Curve (ℂ × ℂ)) (z : α → ℂ) (hz : Tendsto (fun i => (z i).im) l atBot) :
    Tendsto (fun i => ((classicalDiscriminant φ (z i))^2-4) / ((freeDiscriminant (z i))^2-4))
      l (𝓝 1) := by
  simpa only [Pi.mul_apply, shifted_ratios_mul, mul_one] using!
    (tendsto_classicalDiscriminant_sub_div_free_lower φ z hz 2).mul
      (tendsto_classicalDiscriminant_sub_div_free_lower φ z hz (-2))

end NLS.ZakharovShabat
