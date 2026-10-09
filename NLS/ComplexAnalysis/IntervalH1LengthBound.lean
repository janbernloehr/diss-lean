import NLS.ComplexAnalysis.IntervalH1Variation

/-! # Length dependence of the integral H1 trace estimate

The interval length is kept explicit. This does not identify the integral
norm with the unspecified local norm in the printed Lemma G.2.
-/
noncomputable section
open Set MeasureTheory
open NLS.FunctionalAnalysis
namespace NLS.ComplexAnalysis

/-- Both endpoint values and the variation on [0,t] are controlled together
by any sampled value and twice the variation on [0,T]. -/
theorem endpoint_variation_le_sample_interval (f : ℝ → ℂ) (T : ℝ) (hT : 0 < T)
    (hf : AbsolutelyContinuousOnInterval f 0 T)
    (hd : IntervalIntegrable (deriv f) volume 0 T)
    (t s : Icc (0 : ℝ) T) :
    ‖f 0‖+‖f t‖+(∫ r in 0..t.val, ‖deriv f r‖) ≤
      2*‖f s‖+2*(∫ r in (0 : ℝ)..T, ‖deriv f r‖) := by
  have hsub (a b : Icc (0 : ℝ) T) : uIcc a.val b.val ⊆ uIcc (0 : ℝ) T := by
    rw [uIcc_of_le hT.le]
    exact uIcc_subset_Icc a.property b.property
  have hder (a b : Icc (0 : ℝ) T) :
      (∫ r in a.val..b.val, deriv f r) = f b-f a :=
    integral_deriv_eq_sub_complex (hf.mono (hsub a b)) (hd.mono_set (hsub a b))
  have hnorm (a b : Icc (0 : ℝ) T) (hab : a ≤ b) :
      ‖f a-f b‖ ≤ ∫ r in a.val..b.val, ‖deriv f r‖ := by
    rw [norm_sub_rev,← hder a b]
    exact intervalIntegral.norm_integral_le_integral_norm hab
  have h0 : ‖f 0‖ ≤ ‖f s‖+(∫ r in 0..s.val, ‖deriv f r‖) := by
    have h := norm_add_le (f 0-f s) (f s)
    simp only [sub_add_cancel] at h
    exact h.trans (by linarith [hnorm ⟨0,le_rfl,hT.le⟩ s s.property.1])
  have hmono (a : Icc (0 : ℝ) T) :
      (∫ r in 0..a.val, ‖deriv f r‖) ≤ ∫ r in (0 : ℝ)..T, ‖deriv f r‖ :=
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
      (hd.norm.mono_set (hsub ⟨0,le_rfl,hT.le⟩ s))
      (hd.norm.mono_set (hsub s t))
    linarith [hmono t]
  · have ht : ‖f t‖ ≤ ‖f s‖+(∫ r in t.val..s.val, ‖deriv f r‖) := by
      have h := norm_add_le (f t-f s) (f s)
      simp only [sub_add_cancel] at h
      linarith [hnorm t s hts]
    have hi := intervalIntegral.integral_add_adjacent_intervals
      (hd.norm.mono_set (hsub ⟨0,le_rfl,hT.le⟩ t))
      (hd.norm.mono_set (hsub t s))
    linarith [hmono s]

/-- Average the combined trace estimate, keeping the coefficient two
on both the function and its derivative. -/
theorem endpoint_variation_le_integrals_interval (f : ℝ → ℂ) (T : ℝ) (hT : 0 < T)
    (hf : AbsolutelyContinuousOnInterval f 0 T)
    (hfi : IntervalIntegrable f volume 0 T)
    (hd : IntervalIntegrable (deriv f) volume 0 T)
    (t : Icc (0 : ℝ) T) :
    T*(‖f 0‖+‖f t‖+(∫ r in 0..t.val, ‖deriv f r‖)) ≤
      2*(∫ r in (0 : ℝ)..T, ‖f r‖)+2*T*(∫ r in (0 : ℝ)..T, ‖deriv f r‖) := by
  have h := intervalIntegral.integral_mono_on hT.le
    (intervalIntegrable_const (c := ‖f 0‖+‖f t‖+(∫ r in 0..t.val, ‖deriv f r‖)))
    ((hfi.norm.const_mul 2).add (intervalIntegrable_const))
    (fun s hs => endpoint_variation_le_sample_interval f T hT hf hd t ⟨s,hs⟩)
  rw [intervalIntegral.integral_add (hfi.norm.const_mul 2) intervalIntegrable_const] at h
  simpa [intervalIntegral.integral_const_mul,mul_assoc,mul_left_comm,mul_comm,mul_add] using h


/-- The two-dimensional Cauchy--Schwarz estimate, with an explicit energy. -/
theorem linear_combination_le_H1_energy {a b X Y H : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hH : 0 ≤ H)
    (hE : H^2 = X^2+Y^2) :
    a*X+b*Y ≤ Real.sqrt (a^2+b^2)*H := by
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  calc
    (a*X+b*Y)^2 ≤ (a^2+b^2)*(X^2+Y^2) := by nlinarith [sq_nonneg (a*Y-b*X)]
    _ = (Real.sqrt (a^2+b^2)*H)^2 := by
      rw [mul_pow,Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)),hE]

/-- The integral H1 bound at every intermediate time, on an interval of
arbitrary positive length. The length-dependent constant is explicit. -/
theorem endpoint_variation_le_length_H1 (f : ℝ → ℂ) (T : ℝ) (hT : 0 < T)
    (hf : AbsolutelyContinuousOnInterval f 0 T)
    (hL2 : MemLp f 2 (volume.restrict (Ioc 0 T)))
    (hdL2 : MemLp (deriv f) 2 (volume.restrict (Ioc 0 T)))
    (t : Icc (0 : ℝ) T) :
    ‖f 0‖+‖f t‖+(∫ r in 0..t.val, ‖deriv f r‖) ≤
      2*Real.sqrt (T⁻¹+T)*intervalH1Norm f T := by
  have hi : IntervalIntegrable f volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr (hL2.integrable (by norm_num))
  have hdi : IntervalIntegrable (deriv f) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr (hdL2.integrable (by norm_num))
  have hsq : IntervalIntegrable (fun r => ‖f r‖^2) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr
      ((memLp_two_iff_integrable_sq hL2.norm.aestronglyMeasurable).mp hL2.norm)
  have hdsq : IntervalIntegrable (fun r => ‖deriv f r‖^2) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).mpr
      ((memLp_two_iff_integrable_sq hdL2.norm.aestronglyMeasurable).mp hdL2.norm)
  have hf0 := intervalIntegral.integral_nonneg (μ := volume) hT.le (fun r _ => sq_nonneg ‖f r‖)
  have hd0 := intervalIntegral.integral_nonneg (μ := volume) hT.le (fun r _ => sq_nonneg ‖deriv f r‖)
  have hE : intervalH1Norm f T ^ 2 =
      (∫ r in (0 : ℝ)..T, ‖f r‖^2)+(∫ r in (0 : ℝ)..T, ‖deriv f r‖^2) := by
    rw [intervalH1Norm_sq _ _ hT.le,intervalIntegral.integral_add hsq hdsq]
  have hfn := integral_norm_le_sqrt_length_mul_L2 f T hT.le hL2
  have hdn := integral_norm_le_sqrt_length_mul_L2 (deriv f) T hT.le hdL2
  have havg := endpoint_variation_le_integrals_interval f T hT hf hi hdi t
  have hr : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hc : T*(Real.sqrt T)⁻¹ = Real.sqrt T := by
    conv_lhs => arg 1; rw [← Real.mul_self_sqrt hT.le]
    rw [mul_assoc,mul_inv_cancel₀ hr.ne',mul_one]
  have htrace : ‖f 0‖+‖f t‖+(∫ r in 0..t.val, ‖deriv f r‖) ≤
      2*((Real.sqrt T)⁻¹*Real.sqrt (∫ r in (0 : ℝ)..T, ‖f r‖^2)+
        Real.sqrt T*Real.sqrt (∫ r in (0 : ℝ)..T, ‖deriv f r‖^2)) := by
    apply (mul_le_mul_iff_right₀ hT).mp
    calc
      _ ≤ 2*(Real.sqrt T*Real.sqrt (∫ r in (0 : ℝ)..T, ‖f r‖^2))+
          2*T*(Real.sqrt T*Real.sqrt (∫ r in (0 : ℝ)..T, ‖deriv f r‖^2)) := by
        nlinarith [mul_le_mul_of_nonneg_left hdn hT.le]
      _ = 2*(T*(Real.sqrt T)⁻¹)*Real.sqrt (∫ r in (0 : ℝ)..T, ‖f r‖^2)+
          2*T*(Real.sqrt T*Real.sqrt (∫ r in (0 : ℝ)..T, ‖deriv f r‖^2)) := by rw [hc]; ring
      _ = _ := by ring
  have hcs := linear_combination_le_H1_energy (inv_nonneg.mpr hr.le) hr.le
    (Real.sqrt_nonneg (∫ r in (0 : ℝ)..T, ‖f r‖^2))
    (Real.sqrt_nonneg (∫ r in (0 : ℝ)..T, ‖deriv f r‖^2)) (intervalH1Norm_nonneg f T)
    (by rw [Real.sq_sqrt hf0,Real.sq_sqrt hd0]; exact hE)
  have hcoef : (Real.sqrt T)⁻¹^2+(Real.sqrt T)^2 = T⁻¹+T := by
    rw [inv_pow,Real.sq_sqrt hT.le]
  rw [hcoef] at hcs
  exact htrace.trans (by nlinarith)

end NLS.ComplexAnalysis
