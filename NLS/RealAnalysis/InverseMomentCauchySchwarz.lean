import NLS.FunctionalAnalysis.VariableForcingGronwall

/-! Cauchy--Schwarz for a positive angular weight and a positive spectral
coordinate. The estimate retains both the direct and inverse moments. -/
noncomputable section
open Set MeasureTheory intervalIntegral
namespace NLS.RealAnalysis

theorem integral_inverse_moment_cauchySchwarz (m z : ℝ → ℝ)
    (hm : Continuous m) (hz : Continuous z) (hzpos : ∀ t, 0 < z t)
    (T : ℝ) (hT : 0 ≤ T) (hm0 : ∀ t ∈ Icc 0 T, 0 ≤ m t) :
    (∫ t in (0:ℝ)..T, m t)^2 ≤
      (∫ t in (0:ℝ)..T, m t*z t)*(∫ t in (0:ℝ)..T, m t/z t) := by
  let f : ℝ → ℝ := fun t => Real.sqrt (m t*z t)
  let g : ℝ → ℝ := fun t => Real.sqrt (m t/z t)
  have hf : Continuous f := Real.continuous_sqrt.comp (hm.mul hz)
  have hg : Continuous g := Real.continuous_sqrt.comp (hm.div hz (fun t => (hzpos t).ne'))
  have hcs := NLS.FunctionalAnalysis.integral_mul_le_sqrt_sq_mul_sqrt_sq f g hf hg T hT
    (fun t _ => Real.sqrt_nonneg _) (fun t _ => Real.sqrt_nonneg _)
  have hfg : (∫ t in (0:ℝ)..T, f t*g t)=(∫ t in (0:ℝ)..T, m t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hT] at ht
    dsimp only [f,g]
    rw [← Real.sqrt_mul (mul_nonneg (hm0 t ht) (hzpos t).le)]
    have he : (m t*z t)*(m t/z t)=(m t)^2 := by field_simp [(hzpos t).ne']
    rw [he,Real.sqrt_sq_eq_abs,abs_of_nonneg (hm0 t ht)]
  have hff : (∫ t in (0:ℝ)..T, (f t)^2)=(∫ t in (0:ℝ)..T, m t*z t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact Real.sq_sqrt (mul_nonneg (hm0 t ht) (hzpos t).le)
  have hgg : (∫ t in (0:ℝ)..T, (g t)^2)=(∫ t in (0:ℝ)..T, m t/z t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact Real.sq_sqrt (div_nonneg (hm0 t ht) (hzpos t).le)
  rw [hfg,hff,hgg] at hcs
  have hA : 0 ≤ ∫ t in (0:ℝ)..T, m t*z t :=
    intervalIntegral.integral_nonneg hT (fun t ht => mul_nonneg (hm0 t ht) (hzpos t).le)
  have hB : 0 ≤ ∫ t in (0:ℝ)..T, m t/z t :=
    intervalIntegral.integral_nonneg hT (fun t ht => div_nonneg (hm0 t ht) (hzpos t).le)
  have hM : 0 ≤ ∫ t in (0:ℝ)..T, m t := intervalIntegral.integral_nonneg hT hm0
  have hs : (Real.sqrt (∫ t in (0:ℝ)..T, m t*z t)*
      Real.sqrt (∫ t in (0:ℝ)..T, m t/z t))^2=
      (∫ t in (0:ℝ)..T, m t*z t)*(∫ t in (0:ℝ)..T, m t/z t) := by
    rw [mul_pow,Real.sq_sqrt hA,Real.sq_sqrt hB]
  nlinarith [Real.sqrt_nonneg (∫ t in (0:ℝ)..T, m t*z t),
    Real.sqrt_nonneg (∫ t in (0:ℝ)..T, m t/z t)]

end NLS.RealAnalysis
