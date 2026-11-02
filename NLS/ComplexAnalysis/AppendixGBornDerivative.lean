import NLS.ComplexAnalysis.IntervalH1LengthBound
import NLS.ComplexAnalysis.ScalarDuhamel

/-! # The time derivative of the Appendix G Born integral

The exact derivative retains both half-weighted endpoint terms. Its
positive bound uses the explicit integral H1 norm and interval length.
-/
noncomputable section
open Set Complex MeasureTheory
namespace NLS.ComplexAnalysis

/-- Factor the time dependence out of the oscillatory integral. -/
theorem appendixG_oscillatoryIntegral_factor (c : ℂ) (f : ℝ → ℂ) (t : ℝ) :
    oscillatoryIntegral c t f =
      exp (c*t)*(∫ s in (0 : ℝ)..t, exp ((-2*c)*s)*f s) := by
  rw [oscillatoryIntegral,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only [oscillatoryKernel]
  rw [← mul_assoc,← exp_add]
  congr 2
  push_cast
  ring

/-- Differentiation in terminal time, with the actual boundary term. -/
theorem appendixG_hasDerivAt_oscillatoryIntegral (c : ℂ) (f : ℝ → ℂ)
    (hf : Continuous f) (t : ℝ) :
    HasDerivAt (fun u => oscillatoryIntegral c u f)
      (c*oscillatoryIntegral c t f+exp (-c*t)*f t) t := by
  have hc : Continuous (fun s : ℝ => exp ((-2*c)*s)*f s) := by fun_prop
  have hi := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter volume (nhds t)) hc.continuousAt
  have hd := (hasDerivAt_complex_exp_mul c t).mul hi
  simp_rw [appendixG_oscillatoryIntegral_factor]
  apply hd.congr_deriv
  have he : exp (c*t)*exp ((-2*c)*t) = exp (-c*t) := by
    rw [← exp_add]
    congr 1
    ring
  linear_combination (f t)*he

/-- Integration by parts gives the two half-weighted endpoint terms,
including zero spectral parameter without a division. -/
theorem appendixG_oscillatoryIntegral_derivative_parts (c : ℂ) (f : ℝ → ℂ)
    (hf : Continuous f) (t : ℝ)
    (ha : AbsolutelyContinuousOnInterval f 0 t)
    (hd : IntervalIntegrable (deriv f) volume 0 t) :
    deriv (fun u => oscillatoryIntegral c u f) t =
      (exp (-c*t)*f t+exp (c*t)*f 0+oscillatoryIntegral c t (deriv f))/2 := by
  rw [(appendixG_hasDerivAt_oscillatoryIntegral c f hf t).deriv]
  linear_combination (1/2 : ℂ)*oscillatoryIntegral_parts c t f ha hd

/-- The derivative bound with explicit endpoint values and variation. -/
theorem appendixG_oscillatoryIntegral_derivative_weighted_le
    (c : ℂ) (f : ℝ → ℂ) (hf : Continuous f) (t : ℝ) (ht : 0 ≤ t)
    (ha : AbsolutelyContinuousOnInterval f 0 t)
    (hd : IntervalIntegrable (deriv f) volume 0 t) :
    Real.exp (-(|c.re| * t))*‖deriv (fun u => oscillatoryIntegral c u f) t‖ ≤
      (‖f 0‖+‖f t‖+∫ s in 0..t, ‖deriv f s‖)/2 := by
  let E := Real.exp (|c.re| * t)
  have h0 : ‖exp (c*t)‖ ≤ E := by
    simpa only [oscillatoryKernel,mul_zero,sub_zero] using
      norm_oscillatoryKernel_le c t 0 ⟨le_rfl,ht⟩
  have hlast : ‖exp (-c*t)‖ ≤ E := by
    have h := norm_oscillatoryKernel_le c t t ⟨ht,le_rfl⟩
    convert h using 1
    congr 2
    push_cast
    ring
  have hi : ‖oscillatoryIntegral c t (deriv f)‖ ≤ E*(∫ s in 0..t, ‖deriv f s‖) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.norm_integral_le_of_norm_le ht
    · filter_upwards [] with s hs
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_oscillatoryKernel_le c t s ⟨hs.1.le,hs.2⟩) (norm_nonneg _)
    · exact hd.norm.const_mul E
  have hbound : ‖deriv (fun u => oscillatoryIntegral c u f) t‖ ≤
      E*((‖f 0‖+‖f t‖+∫ s in 0..t, ‖deriv f s‖)/2) := by
    rw [appendixG_oscillatoryIntegral_derivative_parts c f hf t ha hd,norm_div]
    norm_num only [norm_ofNat]
    apply (div_le_div_of_nonneg_right
      ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl))
      (by norm_num : (0 : ℝ) ≤ 2)).trans
    simp only [norm_mul]
    have hleft := mul_le_mul_of_nonneg_right hlast (norm_nonneg (f t))
    have hright := mul_le_mul_of_nonneg_right h0 (norm_nonneg (f 0))
    nlinarith
  have h := mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg (-(|c.re| * t)))
  apply h.trans_eq
  dsimp [E]
  rw [← mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]

/-- A uniform positive bound on every intermediate time of an arbitrary
interval, in the explicit integral H1 norm. -/
theorem appendixG_oscillatoryIntegral_derivative_interval_H1
    (T : ℝ) (hT : 0 < T) (c : ℂ) (f : ℝ → ℂ) (hf : Continuous f)
    (ha : AbsolutelyContinuousOnInterval f 0 T)
    (hL2 : MemLp f 2 (volume.restrict (Ioc 0 T)))
    (hdL2 : MemLp (deriv f) 2 (volume.restrict (Ioc 0 T)))
    (t : Icc (0 : ℝ) T) :
    Real.exp (-(|c.re| * t.val))*‖deriv (fun u => oscillatoryIntegral c u f) t‖ ≤
      Real.sqrt (T⁻¹+T)*intervalH1Norm f T := by
  have hsub : uIcc 0 t.val ⊆ uIcc (0 : ℝ) T := by
    rw [uIcc_of_le t.property.1,uIcc_of_le hT.le]
    exact Icc_subset_Icc le_rfl t.property.2
  have hd : IntervalIntegrable (deriv f) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr
      (hdL2.integrable (by norm_num))
  have h := appendixG_oscillatoryIntegral_derivative_weighted_le c f hf t t.property.1
    (ha.mono hsub) (hd.mono_set hsub)
  have htrace := endpoint_variation_le_length_H1 f T hT ha hL2 hdL2 t
  linarith

end NLS.ComplexAnalysis
