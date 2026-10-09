import NLS.ComplexAnalysis.OscillatoryIntegralL2

/-! # Combined endpoint control in the integral H1 norm

The integral convention is explicit. Combining the two traces with the
variation before estimating gives the constant three on the unit interval.
-/
noncomputable section
open Set MeasureTheory
open NLS.FunctionalAnalysis
namespace NLS.ComplexAnalysis

/-- The unnormalized integral H1 norm of a complex function on [0,t]. -/
def intervalH1Norm (f : ℝ → ℂ) (t : ℝ) : ℝ :=
  Real.sqrt (∫ s in 0..t, ‖f s‖^2+‖deriv f s‖^2)

theorem intervalH1Norm_nonneg (f : ℝ → ℂ) (t : ℝ) : 0 ≤ intervalH1Norm f t :=
  Real.sqrt_nonneg _

/-- This size is exactly the square root of the actual integral energy. -/
theorem intervalH1Norm_sq (f : ℝ → ℂ) (t : ℝ) (ht : 0 ≤ t) :
    intervalH1Norm f t ^ 2 = ∫ s in 0..t, ‖f s‖^2+‖deriv f s‖^2 :=
  Real.sq_sqrt (intervalIntegral.integral_nonneg ht
    (fun _s _ => add_nonneg (sq_nonneg _) (sq_nonneg _)))

/-- Square integrability of the function and derivative makes the energy integrable. -/
theorem intervalIntegrable_H1_integrand (f : ℝ → ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hf : MemLp f 2 (volume.restrict (Ioc 0 t)))
    (hd : MemLp (deriv f) 2 (volume.restrict (Ioc 0 t))) :
    IntervalIntegrable (fun s => ‖f s‖^2+‖deriv f s‖^2) volume 0 t := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr
  exact ((memLp_two_iff_integrable_sq hf.norm.aestronglyMeasurable).mp hf.norm).add
    ((memLp_two_iff_integrable_sq hd.norm.aestronglyMeasurable).mp hd.norm)

/-- Both endpoint values and the variation on [0,t] are controlled together
by any sampled value and twice the variation on [0,1]. -/
theorem endpoint_variation_le_sample (f : ℝ → ℂ)
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hd : IntervalIntegrable (deriv f) volume 0 1)
    (t s : Icc (0 : ℝ) 1) :
    ‖f 0‖+‖f t‖+(∫ r in 0..t.val, ‖deriv f r‖) ≤
      2*‖f s‖+2*(∫ r in (0 : ℝ)..1, ‖deriv f r‖) := by
  have hsub (a b : Icc (0 : ℝ) 1) : uIcc a.val b.val ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact uIcc_subset_Icc a.property b.property
  have hder (a b : Icc (0 : ℝ) 1) :
      (∫ r in a.val..b.val, deriv f r) = f b-f a :=
    integral_deriv_eq_sub_complex (hf.mono (hsub a b)) (hd.mono_set (hsub a b))
  have hnorm (a b : Icc (0 : ℝ) 1) (hab : a ≤ b) :
      ‖f a-f b‖ ≤ ∫ r in a.val..b.val, ‖deriv f r‖ := by
    rw [norm_sub_rev,← hder a b]
    exact intervalIntegral.norm_integral_le_integral_norm hab
  have h0 : ‖f 0‖ ≤ ‖f s‖+(∫ r in 0..s.val, ‖deriv f r‖) := by
    have h := norm_add_le (f 0-f s) (f s)
    simp only [sub_add_cancel] at h
    exact h.trans (by linarith [hnorm ⟨0,by norm_num,by norm_num⟩ s s.property.1])
  have hmono (a : Icc (0 : ℝ) 1) :
      (∫ r in 0..a.val, ‖deriv f r‖) ≤ ∫ r in (0 : ℝ)..1, ‖deriv f r‖ :=
    intervalIntegral.integral_mono_interval le_rfl a.property.1 a.property.2
      (Filter.Eventually.of_forall (fun r => norm_nonneg (deriv f r))) hd.norm
  rcases le_total s t with hst | hts
  · have ht : ‖f t‖ ≤ ‖f s‖+(∫ r in s.val..t.val, ‖deriv f r‖) := by
      have h := norm_add_le (f t-f s) (f s)
      simp only [sub_add_cancel] at h
      have hn := hnorm s t hst
      rw [norm_sub_rev] at hn
      linarith
    have hi := intervalIntegral.integral_add_adjacent_intervals
      (hd.norm.mono_set (hsub ⟨0,by norm_num,by norm_num⟩ s))
      (hd.norm.mono_set (hsub s t))
    linarith [hmono t]
  · have ht : ‖f t‖ ≤ ‖f s‖+(∫ r in t.val..s.val, ‖deriv f r‖) := by
      have h := norm_add_le (f t-f s) (f s)
      simp only [sub_add_cancel] at h
      linarith [hnorm t s hts]
    have hi := intervalIntegral.integral_add_adjacent_intervals
      (hd.norm.mono_set (hsub ⟨0,by norm_num,by norm_num⟩ t))
      (hd.norm.mono_set (hsub t s))
    linarith [hmono s]

/-- Average the combined trace estimate, keeping the coefficient two
on both the function and its derivative. -/
theorem endpoint_variation_le_integrals (f : ℝ → ℂ)
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hfi : IntervalIntegrable f volume 0 1)
    (hd : IntervalIntegrable (deriv f) volume 0 1)
    (t : Icc (0 : ℝ) 1) :
    ‖f 0‖+‖f t‖+(∫ r in 0..t.val, ‖deriv f r‖) ≤
      2*(∫ r in (0 : ℝ)..1, ‖f r‖)+2*(∫ r in (0 : ℝ)..1, ‖deriv f r‖) := by
  have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (intervalIntegrable_const (c := ‖f 0‖+‖f t‖+(∫ r in 0..t.val, ‖deriv f r‖)))
    ((hfi.norm.const_mul 2).add (intervalIntegrable_const))
    (fun s hs => endpoint_variation_le_sample f hf hd t ⟨s,hs⟩)
  rw [intervalIntegral.integral_add (hfi.norm.const_mul 2) intervalIntegrable_const] at h
  simpa [intervalIntegral.integral_const_mul] using h

/-- The constant three follows from Cauchy--Schwarz and the combined
endpoint estimate. The potential need not satisfy periodic boundary conditions. -/
theorem endpoint_variation_le_three_H1 (f : ℝ → ℂ)
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hL2 : MemLp f 2 (volume.restrict (Ioc 0 1)))
    (hdL2 : MemLp (deriv f) 2 (volume.restrict (Ioc 0 1)))
    (t : Icc (0 : ℝ) 1) :
    ‖f 0‖+‖f t‖+(∫ r in 0..t.val, ‖deriv f r‖) ≤ 3*intervalH1Norm f 1 := by
  have hi : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hL2.integrable (by norm_num))
  have hdi : IntervalIntegrable (deriv f) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (hdL2.integrable (by norm_num))
  have hsq : IntervalIntegrable (fun r => ‖f r‖^2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      ((memLp_two_iff_integrable_sq hL2.norm.aestronglyMeasurable).mp hL2.norm)
  have hdsq : IntervalIntegrable (fun r => ‖deriv f r‖^2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr
      ((memLp_two_iff_integrable_sq hdL2.norm.aestronglyMeasurable).mp hdL2.norm)
  have hf0 := intervalIntegral.integral_nonneg (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (fun r _ => sq_nonneg ‖f r‖)
  have hd0 := intervalIntegral.integral_nonneg (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (fun r _ => sq_nonneg ‖deriv f r‖)
  have hE : intervalH1Norm f 1 ^ 2 =
      (∫ r in (0 : ℝ)..1, ‖f r‖^2)+(∫ r in (0 : ℝ)..1, ‖deriv f r‖^2) := by
    rw [intervalH1Norm,intervalIntegral.integral_add hsq hdsq,Real.sq_sqrt (add_nonneg hf0 hd0)]
  have hfn := integral_norm_le_sqrt_length_mul_L2 f 1 (by norm_num) hL2
  have hdn := integral_norm_le_sqrt_length_mul_L2 (deriv f) 1 (by norm_num) hdL2
  simp only [Real.sqrt_one,one_mul] at hfn hdn
  apply (endpoint_variation_le_integrals f hf hi hdi t).trans
  have hsum : 2*(Real.sqrt (∫ r in (0 : ℝ)..1, ‖f r‖^2)+
      Real.sqrt (∫ r in (0 : ℝ)..1, ‖deriv f r‖^2)) ≤ 3*intervalH1Norm f 1 := by
    nlinarith [Real.sq_sqrt hf0,Real.sq_sqrt hd0,intervalH1Norm_nonneg f 1,
      Real.sqrt_nonneg (∫ r in (0 : ℝ)..1, ‖f r‖^2),
      Real.sqrt_nonneg (∫ r in (0 : ℝ)..1, ‖deriv f r‖^2),
      sq_nonneg (Real.sqrt (∫ r in (0 : ℝ)..1, ‖f r‖^2)-
        Real.sqrt (∫ r in (0 : ℝ)..1, ‖deriv f r‖^2))]
  linarith

end NLS.ComplexAnalysis
