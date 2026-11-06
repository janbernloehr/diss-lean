import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # A real scalar coefficient with a nonzero periodic AC solution has zero mean -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex MeasureTheory Filter Topology
namespace NLS.FunctionalAnalysis

theorem absolutelyContinuous_comp_of_dist_le
    {E F : Type*} [MetricSpace E] [MetricSpace F] {f : ℝ → E} {g : E → F}
    {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b,
      dist (g (f x)) (g (f y)) ≤ C*dist (f x) (f y)) :
    AbsolutelyContinuousOnInterval (g ∘ f) a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  have hpos : 0 < C+1 := by linarith
  obtain ⟨δ,hδ,hprop⟩ := hf (ε/(C+1)) (div_pos hε hpos)
  refine ⟨δ,hδ,?_⟩
  intro intervals hi hl
  calc
    _ ≤ C*∑ i ∈ Finset.range intervals.1, dist (f (intervals.2 i).1) (f (intervals.2 i).2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i hii => hbound _ (hi.1 i hii).1 _ (hi.1 i hii).2)
    _ ≤ (C+1)*∑ i ∈ Finset.range intervals.1, dist (f (intervals.2 i).1) (f (intervals.2 i).2) :=
      mul_le_mul_of_nonneg_right (by linarith) (Finset.sum_nonneg (fun _ _ => dist_nonneg))
    _ < (C+1)*(ε/(C+1)) := mul_lt_mul_of_pos_left (hprop intervals hi hl) hpos
    _ = ε := mul_div_cancel₀ _ hpos.ne'

theorem absolutelyContinuous_real_exp {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun x => Real.exp (f x)) a b := by
  obtain ⟨B,hB⟩ := hf.exists_bound
  apply absolutelyContinuous_comp_of_dist_le (g := Real.exp) hf (Real.exp B) (Real.exp_pos B).le
  intro x hx y hy
  have hfx : f x ≤ B := (le_abs_self _).trans (hB x hx)
  have hfy : f y ≤ B := (le_abs_self _).trans (hB y hy)
  simpa only [dist_eq_norm] using Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t (_ht : t ∈ Iic B) => Real.differentiableAt_exp)
    (fun t ht => by simpa only [Real.deriv_exp,Real.norm_eq_abs,abs_of_pos (Real.exp_pos t)] using
      Real.exp_le_exp.mpr ht) (convex_Iic B) hfy hfx

/-- The actual coefficient need only be L1, and the solution only AC.
Neither differentiability everywhere nor nonvanishing everywhere is assumed. -/
theorem integral_eq_zero_of_nonzero_periodic_scalar_AC
    (α : ℝ → ℝ) (hα : IntervalIntegrable α volume 0 1)
    (F : ℝ → ℂ) (hF : AbsolutelyContinuousOnInterval F 0 1)
    (hd : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt F ((α x : ℂ)*F x) x)
    (hperiod : F 1 = F 0) (hnon : ∃ x ∈ Icc (0 : ℝ) 1, F x ≠ 0) :
    (∫ x in (0 : ℝ)..1, α x) = 0 := by
  let P : ℝ → ℝ := fun t => ∫ x in (0 : ℝ)..t, α x
  let E : ℝ → ℝ := fun t => Real.exp (-P t)
  have hPa : AbsolutelyContinuousOnInterval P 0 1 := hα.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hEa : AbsolutelyContinuousOnInterval E 0 1 := absolutelyContinuous_real_exp hPa.neg
  have hEaC := absolutelyContinuousOnInterval_clm hEa Complex.ofRealCLM
  change AbsolutelyContinuousOnInterval (fun x => (E x : ℂ)) 0 1 at hEaC
  have hza : AbsolutelyContinuousOnInterval (fun t => (E t : ℂ)*F t) 0 1 := by
    simpa only [Pi.smul_def,smul_eq_mul,Pi.mul_def] using hEaC.smul hF
  rw [restrict_Ioc_eq_restrict_Icc] at hd
  have hdglobal := (ae_restrict_iff' measurableSet_Icc).mp hd
  have hzd : ∀ᵐ x : ℝ, x ∈ uIcc (0 : ℝ) 1 →
      HasDerivAt (fun t => (E t : ℂ)*F t) 0 x := by
    filter_upwards [hdglobal,hα.ae_hasDerivAt_integral] with x hx hpx
    intro hxi
    have hxI : x ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hxi
    have hp : HasDerivAt P (α x) x := hpx hxi 0 (by simp)
    have he : HasDerivAt E (-α x*E x) x := by
      simpa only [E,Pi.neg_apply,mul_comm] using hp.neg.exp
    have hdprod := he.ofReal_comp.mul (hx hxI)
    have hzero : (((-α x*E x : ℝ) : ℂ)*F x+(E x : ℂ)*((α x : ℂ)*F x)) = 0 := by
      push_cast
      ring
    rw [hzero] at hdprod
    exact hdprod
  obtain ⟨c,hc⟩ := hza.const_of_ae_hasDerivAt_zero hzd
  have hc0 := hc 0 (by simp)
  have hc1 := hc 1 (by simp)
  have hE0 : E 0 = 1 := by simp [E,P]
  rw [hE0,ofReal_one,one_mul] at hc0
  have hF0 : F 0 ≠ 0 := by
    intro hzero
    obtain ⟨x,hx,hFx⟩ := hnon
    have hcx := hc x (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx)
    rw [←hc0,hzero] at hcx
    exact hFx ((mul_eq_zero.mp hcx).resolve_left (ofReal_ne_zero.mpr (Real.exp_ne_zero _)))
  have hE1 : E 1 = 1 := by
    apply ofReal_injective
    apply mul_right_cancel₀ hF0
    simpa only [ofReal_one,one_mul,hperiod,←hc0] using hc1
  have hP1 : -P 1 = 0 := Real.exp_injective (hE1.trans Real.exp_zero.symm)
  simpa only [P,neg_eq_zero] using hP1

end NLS.FunctionalAnalysis
