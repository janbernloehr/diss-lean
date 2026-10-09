import NLS.FunctionalAnalysis.VariableGronwall
import Mathlib.MeasureTheory.Function.L2Space

/-! # Variable-forcing Volterra estimates with an L2 budget

The forcing keeps its actual time dependence. An integrating factor and
Cauchy--Schwarz give the coefficient A*exp(A) on intervals of length at most
one, where A is an L2 bound for the variable coupling. This is the scalar
estimate needed for Appendix G.1; no bound on the unknown error is assumed.
-/
noncomputable section
open Set MeasureTheory
namespace NLS.FunctionalAnalysis

/-- Close a variable-coefficient Volterra inequality while retaining the
terminal forcing value and the integral of coupling times forcing. -/
theorem le_forcing_add_exp_integral_mul
    (f F a : ℝ → ℝ) (hf : Continuous f) (hF : Continuous F) (ha : Continuous a)
    (T : ℝ) (hT : 0 ≤ T)
    (ha0 : ∀ t ∈ Icc 0 T, 0 ≤ a t) (hF0 : ∀ t ∈ Icc 0 T, 0 ≤ F t)
    (hbound : ∀ t ∈ Icc 0 T, f t ≤ F t + ∫ s in (0:ℝ)..t, a s*f s) :
    f T ≤ F T + Real.exp (∫ s in (0:ℝ)..T, a s)*(∫ s in (0:ℝ)..T, a s*F s) := by
  let A (t : ℝ) := ∫ s in (0:ℝ)..t, a s
  let y (t : ℝ) := ∫ s in (0:ℝ)..t, a s*f s
  have hA (t : ℝ) : HasDerivAt A (a t) t :=
    intervalIntegral.integral_hasDerivAt_right (ha.intervalIntegrable 0 t)
      ha.stronglyMeasurable.stronglyMeasurableAtFilter ha.continuousAt
  have hy (t : ℝ) : HasDerivAt y (a t*f t) t :=
    intervalIntegral.integral_hasDerivAt_right ((ha.mul hf).intervalIntegrable 0 t)
      (ha.mul hf).stronglyMeasurable.stronglyMeasurableAtFilter (ha.mul hf).continuousAt
  have hAc : Continuous A := continuous_iff_continuousAt.mpr (fun t => (hA t).continuousAt)
  have hyc : Continuous y := continuous_iff_continuousAt.mpr (fun t => (hy t).continuousAt)
  let g (t : ℝ) := Real.exp (-A t)*y t
  let g' (t : ℝ) := Real.exp (-A t)*a t*(f t-y t)
  have hg (t : ℝ) : HasDerivAt g (g' t) t := by
    convert! (((hA t).neg.exp).mul (hy t)) using 1
    dsimp [g']
    ring
  have hgc : Continuous g := (Real.continuous_exp.comp hAc.neg).mul hyc
  have hg'c : Continuous g' := ((Real.continuous_exp.comp hAc.neg).mul ha).mul (hf.sub hyc)
  have hle (t : ℝ) (ht : t ∈ Icc 0 T) : g' t ≤ a t*F t := by
    have hAn : 0 ≤ A t := intervalIntegral.integral_nonneg ht.1
      (fun s hs => ha0 s ⟨hs.1,hs.2.trans ht.2⟩)
    have he : Real.exp (-A t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hAn)
    calc
      g' t ≤ Real.exp (-A t)*a t*F t :=
        mul_le_mul_of_nonneg_left (by linarith [hbound t ht])
          (mul_nonneg (Real.exp_nonneg _) (ha0 t ht))
      _ = Real.exp (-A t)*(a t*F t) := by ring
      _ ≤ a t*F t := mul_le_of_le_one_left (mul_nonneg (ha0 t ht) (hF0 t ht)) he
  have hi := intervalIntegral.integral_mono_on (μ := volume) hT (hg'c.intervalIntegrable 0 T)
    ((ha.mul hF).intervalIntegrable 0 T) hle
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hg t) (hg'c.intervalIntegrable 0 T)] at hi
  have hg0 : g 0 = 0 := by simp [g,y]
  rw [hg0,sub_zero] at hi
  have hh := mul_le_mul_of_nonneg_left hi (Real.exp_nonneg (A T))
  have hid : Real.exp (A T)*g T = y T := by
    dsimp [g]
    rw [← mul_assoc,← Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul]
  rw [hid] at hh
  exact (hbound T ⟨hT,le_rfl⟩).trans (add_le_add (le_refl _) hh)

/-- Interval Cauchy--Schwarz for continuous nonnegative scalar functions. -/
theorem integral_mul_le_sqrt_sq_mul_sqrt_sq
    (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (T : ℝ) (hT : 0 ≤ T)
    (hf0 : ∀ t ∈ Icc 0 T, 0 ≤ f t) (hg0 : ∀ t ∈ Icc 0 T, 0 ≤ g t) :
    (∫ t in (0:ℝ)..T, f t*g t) ≤
      Real.sqrt (∫ t in (0:ℝ)..T, (f t)^2)*Real.sqrt (∫ t in (0:ℝ)..T, (g t)^2) := by
  let μ := volume.restrict (Ioc (0:ℝ) T)
  have hf2 : MemLp f 2 μ := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    ((hf.pow 2).intervalIntegrable 0 T).1
  have hg2 : MemLp g 2 μ := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mpr
    ((hg.pow 2).intervalIntegrable 0 T).1
  have hfn : 0 ≤ᵐ[μ] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hf0 t ⟨ht.1.le,ht.2⟩
  have hgn : 0 ≤ᵐ[μ] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hg0 t ⟨ht.1.le,ht.2⟩
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two hfn hgn
    (by simpa using hf2) (by simpa using hg2)
  simpa only [intervalIntegral.integral_of_le hT,Real.sqrt_eq_rpow,Real.rpow_two] using h

/-- The exact A*exp(A) estimate on a subinterval of the unit interval.
A bounds the coupling's L2 norm; the forcing uses its own L2 norm in time. -/
theorem le_forcing_add_L2_bound
    (f F a : ℝ → ℝ) (hf : Continuous f) (hF : Continuous F) (ha : Continuous a)
    (T A : ℝ) (hT : T ∈ Icc (0:ℝ) 1)
    (ha0 : ∀ t ∈ Icc 0 T, 0 ≤ a t) (hF0 : ∀ t ∈ Icc 0 T, 0 ≤ F t)
    (hA : Real.sqrt (∫ s in (0:ℝ)..T, (a s)^2) ≤ A)
    (hbound : ∀ t ∈ Icc 0 T, f t ≤ F t + ∫ s in (0:ℝ)..t, a s*f s) :
    f T ≤ F T + A*Real.exp A*Real.sqrt (∫ s in (0:ℝ)..T, (F s)^2) := by
  have hi : (∫ s in (0:ℝ)..T, a s) ≤ A := by
    have h := integral_mul_le_sqrt_sq_mul_sqrt_sq a (fun _ => 1) ha continuous_const T hT.1
      ha0 (by intros; norm_num)
    simp only [mul_one,one_pow,intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_one] at h
    exact h.trans ((mul_le_mul_of_nonneg_left (Real.sqrt_le_one.mpr hT.2) (Real.sqrt_nonneg _)).trans
      (by simpa using hA))
  have hAF := (integral_mul_le_sqrt_sq_mul_sqrt_sq a F ha hF T hT.1 ha0 hF0).trans
    (mul_le_mul_of_nonneg_right hA (Real.sqrt_nonneg _))
  have hh := le_forcing_add_exp_integral_mul f F a hf hF ha T hT.1 ha0 hF0 hbound
  apply hh.trans
  apply add_le_add (le_refl _)
  calc
    Real.exp (∫ s in (0:ℝ)..T, a s)*(∫ s in (0:ℝ)..T, a s*F s) ≤
        Real.exp A*(A*Real.sqrt (∫ s in (0:ℝ)..T, (F s)^2)) :=
      mul_le_mul (Real.exp_le_exp.mpr hi) hAF
        (intervalIntegral.integral_nonneg hT.1 (fun t ht => mul_nonneg (ha0 t ht) (hF0 t ht)))
        (Real.exp_nonneg _)
    _ = _ := by ring

end NLS.FunctionalAnalysis
