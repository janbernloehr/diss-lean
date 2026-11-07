import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-! # The real quadratic energy change on a nonnegative interval

The principal real square root gives the continuous inverse, including
at zero and for a collapsed interval. The exact integral pullback keeps
the derivative factor two times the original variable.
-/
noncomputable section
set_option autoImplicit false
open Set Real MeasureTheory
namespace NLS.RealAnalysis

theorem sqrt_add_mem_of_mem_squared_interval (l r c E : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r)
    (hE : E ∈ Icc (l^2-c) (r^2-c)) :
    Real.sqrt (E+c) ∈ Icc l r ∧ (Real.sqrt (E+c))^2-c = E := by
  have hnonneg : 0 ≤ E+c := by nlinarith [sq_nonneg l,hE.1]
  have hs := Real.sq_sqrt hnonneg
  have hp := Real.sqrt_nonneg (E+c)
  exact ⟨⟨by nlinarith [hE.1],by nlinarith [hE.2]⟩,by linarith⟩

theorem continuousOn_of_quadratic_pullback (l r c : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r)
    (F g : ℝ → ℝ) (hF : ContinuousOn F (Icc l r))
    (he : ∀ x ∈ Icc l r, g (x^2-c) = F x) :
    ContinuousOn g (Icc (l^2-c) (r^2-c)) := by
  have hs : Continuous (fun E : ℝ => Real.sqrt (E+c)) := Real.continuous_sqrt.comp (continuous_id.add continuous_const)
  have hcomp := hF.comp hs.continuousOn
    (fun E hE => (sqrt_add_mem_of_mem_squared_interval l r c E hl hlr hE).1)
  apply hcomp.congr
  intro E hE
  obtain ⟨hin,heq⟩ := sqrt_add_mem_of_mem_squared_interval l r c E hl hlr hE
  exact ((he _ hin).symm.trans (congrArg g heq)).symm

theorem integral_quadratic_shift (l r c : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r)
    (g : ℝ → ℝ) (hg : ContinuousOn g (Icc (l^2-c) (r^2-c))) :
    (∫ E in (l^2-c)..(r^2-c), g E) = 2*∫ x in l..r, x*g (x^2-c) := by
  let f : ℝ → ℝ := fun x => x^2-c
  have hf : ∀ x ∈ uIcc l r, HasDerivAt f (2*x) x := by
    intro x _
    simpa [f] using ((hasDerivAt_id x).pow 2).sub_const c
  have hmaps : f '' uIcc l r ⊆ Icc (l^2-c) (r^2-c) := by
    rintro y ⟨x,hx,rfl⟩
    rw [uIcc_of_le hlr] at hx
    dsimp only [f]
    constructor <;> nlinarith [hx.1,hx.2]
  have h := intervalIntegral.integral_comp_mul_deriv' hf (by fun_prop) (hg.mono hmaps)
  change (∫ x in l..r, g (x^2-c)*(2*x)) = _ at h
  rw [← h,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  ring

end NLS.RealAnalysis
