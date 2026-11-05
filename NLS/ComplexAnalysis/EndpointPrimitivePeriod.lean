import NLS.ComplexAnalysis.EndpointRootLoopNormalization
import NLS.ComplexAnalysis.SemicircleMean
import NLS.ComplexAnalysis.PiecewiseContourCongruence

/-! # Exact periods of an endpoint-root primitive

Shrinking ellipses compute the actual positively oriented contour
integral as a regular sine-square mean. No boundary integral or contour
normalization is supplied as an assumption.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex MeasureTheory NLS.ZakharovShabat
namespace NLS.ComplexAnalysis

theorem cosine_unitAverage_eq_halfPeriod (f : ℝ → ℂ) (hf : ContinuousOn f (Icc (-1) 1)) :
    (∫ t in (0 : ℝ)..1, f (Real.cos ((2*Real.pi)*t))) =
      (Real.pi : ℂ)⁻¹*(∫ θ in (0 : ℝ)..Real.pi, f (Real.cos θ)) := by
  have hc : Continuous (fun θ : ℝ => f (Real.cos θ)) :=
    hf.comp_continuous Real.continuous_cos (fun θ => ⟨Real.neg_one_le_cos θ,Real.cos_le_one θ⟩)
  have hsecond : (∫ θ in Real.pi..(2*Real.pi), f (Real.cos θ)) =
      ∫ θ in (0 : ℝ)..Real.pi, f (Real.cos θ) := by
    have hh := intervalIntegral.integral_comp_sub_left (fun θ : ℝ => f (Real.cos θ))
      (2*Real.pi) (a := 0) (b := Real.pi)
    simpa only [two_mul,add_sub_cancel_left,sub_zero,Real.cos_sub,Real.cos_add,Real.sin_add,Real.cos_pi,Real.sin_pi,
      neg_mul,neg_neg,one_mul,mul_zero,zero_mul,sub_zero,add_zero] using hh.symm
  have hfull : (∫ θ in (0 : ℝ)..(2*Real.pi), f (Real.cos θ)) =
      (2 : ℂ)*(∫ θ in (0 : ℝ)..Real.pi, f (Real.cos θ)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),hsecond]
    ring
  have hscale := intervalIntegral.smul_integral_comp_mul_left
    (f := fun θ : ℝ => f (Real.cos θ)) (a := 0) (b := 1) (2*Real.pi)
  simp only [mul_zero,mul_one,Complex.real_smul,ofReal_mul,ofReal_ofNat] at hscale
  rw [hfull] at hscale
  have hh : (Real.pi : ℂ)*(∫ t in (0 : ℝ)..1, f (Real.cos ((2*Real.pi)*t))) =
      ∫ θ in (0 : ℝ)..Real.pi, f (Real.cos θ) := by linear_combination hscale/2
  apply mul_left_cancel₀ (show (Real.pi : ℂ) ≠ 0 by exact_mod_cast Real.pi_ne_zero)
  rw [← mul_assoc,mul_inv_cancel₀ (by exact_mod_cast Real.pi_ne_zero),one_mul]
  exact hh

theorem quadratic_cosine_unitAverage_eq_sineSquare
    (t d : ℂ) (S : ℂ → ℂ) (hS : ContinuousOn S (standardRootGapSegment t d)) :
    (∫ a in (0 : ℝ)..1,
      (((t+d*(Real.cos ((2*Real.pi)*a) : ℂ))-t)^2-d^2)*
        S (t+d*(Real.cos ((2*Real.pi)*a) : ℂ))) =
      -(d^2)/(Real.pi : ℂ)*(∫ θ in (0 : ℝ)..Real.pi,
        (Real.sin θ : ℂ)^2*S (t+d*(Real.cos θ : ℂ))) := by
  let f : ℝ → ℂ := fun a => ((d*(a : ℂ))^2-d^2)*S (t+d*(a : ℂ))
  have hf : ContinuousOn f (Icc (-1) 1) := by
    have hg : ContinuousOn (fun a : ℝ => S (t+d*(a : ℂ))) (Icc (-1) 1) :=
      hS.comp (by fun_prop) (fun a ha => ⟨a,ha,rfl⟩)
    exact (by fun_prop : Continuous (fun a : ℝ => (d*(a : ℂ))^2-d^2)).continuousOn.mul hg
  have he := cosine_unitAverage_eq_halfPeriod f hf
  simp only [f,add_sub_cancel_left] at he ⊢
  rw [he]
  have hi : (∫ θ in (0 : ℝ)..Real.pi, ((d*(Real.cos θ : ℂ))^2-d^2)*S (t+d*(Real.cos θ : ℂ))) =
      -(d^2)*(∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ : ℂ)^2*S (t+d*(Real.cos θ : ℂ))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    have hh : (Real.sin θ : ℂ)^2+(Real.cos θ : ℂ)^2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq θ
    linear_combination d^2*S (t+d*(Real.cos θ : ℂ))*hh
  rw [hi]
  ring

theorem exists_endpointPrimitive_ellipse_period
    (c t d : ℂ) (hd : d ≠ 0) (U : Set ℂ) (hU : IsOpen U)
    (hgap : standardRootGapSegment t d ⊆ U) (S : ℂ → ℂ) (hS : AnalyticOnNhd ℂ S U) :
    ∃ R : ℝ, 1 < R ∧ ∀ r : ℝ, ∀ hr : 1 < r, r ≤ R →
      (standardRootEllipseLoop t d r (by linarith)).Inside (U \ standardRootGapSegment t d) ∧
      (standardRootEllipseLoop t d r (by linarith)).windingIntegral t = 1 ∧
      (standardRootEllipseLoop t d r (by linarith)).integral
        (fun z => I/(2*c)*normalizedStandardRoot t ((2*d)^2) z*S z) =
          -(d^2)/c*(∫ θ in (0 : ℝ)..Real.pi, (Real.sin θ : ℂ)^2*S (t+d*(Real.cos θ : ℂ))) := by
  let P : ℂ → ℂ := fun z => (z-t)^2-d^2
  let f : ℂ → ℂ := fun z => P z*S z
  have hf : AnalyticOnNhd ℂ f U :=
    ((analyticOnNhd_id.sub analyticOnNhd_const).pow 2 |>.sub analyticOnNhd_const).mul hS
  obtain ⟨R,hR,hperiod⟩ := exists_standardRootEllipse_local_period t d hd U hU hgap f hf
  refine ⟨R,hR,?_⟩
  intro r hr hrR
  obtain ⟨hin,he⟩ := hperiod r hr hrR
  let Γ := standardRootEllipseLoop t d r (by linarith)
  refine ⟨hin,standardRootEllipseLoop_winding_one t d hd r hr,?_⟩
  have hsame : Γ.integral (fun z => I/(2*c)*normalizedStandardRoot t ((2*d)^2) z*S z) =
      (I/(2*c))*Γ.integral (fun z => f z/normalizedStandardRoot t ((2*d)^2) z) := by
    rw [← Γ.integral_const_mul]
    apply Γ.integral_congr hin
    intro z hz
    dsimp only [f]
    have hm : t ≠ z := fun hh => hz.2 (hh ▸ (show t ∈ standardRootGapSegment t d from ⟨0,by constructor <;> norm_num,by simp⟩))
    have hs := normalizedStandardRoot_sq t ((2*d)^2) z hm
    have hp : P z = normalizedStandardRoot t ((2*d)^2) z^2 := by
      dsimp [P]
      linear_combination -hs
    rw [hp]
    field_simp [standardRoot_ne_zero_off_gap t d z hz.2]
  rw [hsame,he]
  have hmean := quadratic_cosine_unitAverage_eq_sineSquare t d S (hS.continuousOn.mono hgap)
  change (I/(2*c))*((-(2*(Real.pi : ℂ))*I)*(∫ a in (0 : ℝ)..1,
      (((t+d*(Real.cos ((2*Real.pi)*a) : ℂ))-t)^2-d^2)*S (t+d*(Real.cos ((2*Real.pi)*a) : ℂ)))) = _
  rw [hmean]
  field_simp
  rw [I_sq]
  ring

end NLS.ComplexAnalysis
