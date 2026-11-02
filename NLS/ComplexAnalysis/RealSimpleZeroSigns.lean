import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-! # Signs across a simple real analytic zero

A real restriction of an analytic function cannot have a local extremum
at a simple zero. Continuity propagates a strict sign on a connected
zero-free interval. Together these give the opposite sign across an
order-one endpoint, without a prior derivative-sign convention.
-/

noncomputable section
open Set Filter Topology Complex
namespace NLS.ComplexAnalysis

theorem not_isLocalExtr_of_simple_real_zero (F : ℂ → ℂ) (a : ℝ)
    (hf : AnalyticAt ℂ F (a : ℂ)) (hr : ∀ t : ℝ, (F t).im = 0)
    (ho : analyticOrderNatAt F a = 1) :
    ¬ IsLocalExtr (fun t : ℝ => (F t).re) a := by
  intro hext
  have hd := hf.differentiableAt.hasDerivAt
  have hre : (deriv F (a : ℂ)).re = 0 := hext.hasDerivAt_eq_zero hd.real_of_complex
  have him : HasDerivAt (fun t : ℝ => (F t).im) (deriv F (a : ℂ)).im a :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt a hd.comp_ofReal
  have he : (fun t : ℝ => (F t).im) = fun _ => (0 : ℝ) := funext hr
  rw [he] at him
  have himzero : (deriv F (a : ℂ)).im = 0 := him.unique (hasDerivAt_const a (0 : ℝ))
  have hd0 : deriv F (a : ℂ) = 0 := Complex.ext hre himzero
  have hz : F (a : ℂ) = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero (by omega)
  have hfinite : analyticOrderAt F (a : ℂ) ≠ ⊤ := by
    intro hh
    simp [analyticOrderNatAt,hh] at ho
  have horder : analyticOrderAt F (a : ℂ) = 1 := by
    have hh := congrArg (fun k : ℕ => (k : ℕ∞)) ho
    simpa only [Nat.cast_analyticOrderNatAt hfinite,Nat.cast_one] using hh
  have htwo : (2 : ℕ∞) ≤ analyticOrderAt F (a : ℂ) :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hf).mpr (by
      intro i hi
      interval_cases i <;> simp [iteratedDeriv_zero,iteratedDeriv_one,hz,hd0])
  rw [horder] at htwo
  norm_num at htwo

theorem negative_on_preconnected_of_nonzero
    (g : ℝ → ℝ) (S : Set ℝ) (hS : IsPreconnected S) (hg : ContinuousOn g S)
    (hne : ∀ x ∈ S, g x ≠ 0) (y : ℝ) (hy : y ∈ S) (hgy : g y < 0)
    (x : ℝ) (hx : x ∈ S) : g x < 0 := by
  by_contra hh
  have hc := hS.image g hg
  have hz : (0 : ℝ) ∈ g '' S := hc.Icc_subset ⟨y,hy,rfl⟩ ⟨x,hx,rfl⟩ ⟨hgy.le,not_lt.mp hh⟩
  obtain ⟨z,hz,hzero⟩ := hz
  exact hne z hz hzero

theorem positive_right_of_negative_left
    (F : ℂ → ℂ) (hf : AnalyticOnNhd ℂ F univ) (hr : ∀ t : ℝ, (F t).im = 0)
    (b a c : ℝ) (hba : b < a) (hac : a < c) (ho : analyticOrderNatAt F a = 1)
    (hleft : ∀ t ∈ Ioo b a, (F t).re < 0)
    (hright : ∀ t ∈ Ioo a c, F t ≠ 0) :
    ∀ x ∈ Ioo a c, 0 < (F x).re := by
  intro x hx
  have hcont : Continuous (fun t : ℝ => (F t).re) :=
    Complex.continuous_re.comp (hf.continuous.comp Complex.continuous_ofReal)
  have hne (t : ℝ) (ht : t ∈ Ioo a c) : (F t).re ≠ 0 := by
    intro hz
    exact hright t ht (Complex.ext hz (hr t))
  by_contra hh
  have hneg : (F x).re < 0 := lt_of_le_of_ne (not_lt.mp hh) (hne x hx)
  have hnegative : ∀ t ∈ Ioo a c, (F t).re < 0 :=
    negative_on_preconnected_of_nonzero _ _ isPreconnected_Ioo hcont.continuousOn hne x hx hneg
  have hz : F (a : ℂ) = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero (by omega)
  apply not_isLocalExtr_of_simple_real_zero F a (hf a (mem_univ _)) hr ho
  apply Or.inr
  filter_upwards [Ioo_mem_nhds hba hac] with t ht
  change (F t).re ≤ (F (a : ℂ)).re
  rw [hz,zero_re]
  rcases lt_trichotomy t a with hta | rfl | hat
  · exact (hleft t ⟨ht.1,hta⟩).le
  · simp [hz]
  · exact (hnegative t ⟨hat,ht.2⟩).le

theorem positive_left_of_negative_right
    (F : ℂ → ℂ) (hf : AnalyticOnNhd ℂ F univ) (hr : ∀ t : ℝ, (F t).im = 0)
    (b a c : ℝ) (hba : b < a) (hac : a < c) (ho : analyticOrderNatAt F a = 1)
    (hleft : ∀ t ∈ Ioo b a, F t ≠ 0)
    (hright : ∀ t ∈ Ioo a c, (F t).re < 0) :
    ∀ x ∈ Ioo b a, 0 < (F x).re := by
  intro x hx
  have hcont : Continuous (fun t : ℝ => (F t).re) :=
    Complex.continuous_re.comp (hf.continuous.comp Complex.continuous_ofReal)
  have hne (t : ℝ) (ht : t ∈ Ioo b a) : (F t).re ≠ 0 := by
    intro hz
    exact hleft t ht (Complex.ext hz (hr t))
  by_contra hh
  have hneg : (F x).re < 0 := lt_of_le_of_ne (not_lt.mp hh) (hne x hx)
  have hnegative : ∀ t ∈ Ioo b a, (F t).re < 0 :=
    negative_on_preconnected_of_nonzero _ _ isPreconnected_Ioo hcont.continuousOn hne x hx hneg
  have hz : F (a : ℂ) = 0 := apply_eq_zero_of_analyticOrderNatAt_ne_zero (by omega)
  apply not_isLocalExtr_of_simple_real_zero F a (hf a (mem_univ _)) hr ho
  apply Or.inr
  filter_upwards [Ioo_mem_nhds hba hac] with t ht
  change (F t).re ≤ (F (a : ℂ)).re
  rw [hz,zero_re]
  rcases lt_trichotomy t a with hta | rfl | hat
  · exact (hnegative t ⟨ht.1,hta⟩).le
  · simp [hz]
  · exact (hright t ⟨hat,ht.2⟩).le

/-- A continuous branch issuing from a positive level cannot pass to the
negative square-root branch without entering the forbidden squared range. -/
theorem above_pos_level_of_square_gt
    (g : ℝ → ℝ) (hg : Continuous g) (a b c : ℝ) (hab : a < b) (hc : 0 < c)
    (ha : g a = c) (hsq : ∀ t ∈ Ioc a b, c^2 < (g t)^2) : c < g b := by
  by_contra hh
  have hgb : g b < 0 := by
    by_contra hn
    have hm := mul_self_le_mul_self (not_lt.mp hn) (not_lt.mp hh)
    have hs := hsq b ⟨hab,le_rfl⟩
    nlinarith
  obtain ⟨t,ht,hzero⟩ := intermediate_value_Icc' hab.le hg.continuousOn
    (show (0 : ℝ) ∈ Icc (g b) (g a) by rw [ha]; exact ⟨hgb.le,hc.le⟩)
  have hat : a < t := lt_of_le_of_ne ht.1 (by intro he; rw [← he,ha] at hzero; linarith)
  have hs := hsq t ⟨hat,ht.2⟩
  rw [hzero] at hs
  nlinarith [sq_nonneg c]

theorem above_pos_level_of_square_gt_left
    (g : ℝ → ℝ) (hg : Continuous g) (a b c : ℝ) (hab : a < b) (hc : 0 < c)
    (hb : g b = c) (hsq : ∀ t ∈ Ico a b, c^2 < (g t)^2) : c < g a := by
  by_contra hh
  have hga : g a < 0 := by
    by_contra hn
    have hm := mul_self_le_mul_self (not_lt.mp hn) (not_lt.mp hh)
    have hs := hsq a ⟨le_rfl,hab⟩
    nlinarith
  obtain ⟨t,ht,hzero⟩ := intermediate_value_Icc hab.le hg.continuousOn
    (show (0 : ℝ) ∈ Icc (g a) (g b) by rw [hb]; exact ⟨hga.le,hc.le⟩)
  have htb : t < b := lt_of_le_of_ne ht.2 (by intro he; rw [he,hb] at hzero; linarith)
  have hs := hsq t ⟨ht.1,htb⟩
  rw [hzero] at hs
  nlinarith [sq_nonneg c]

end NLS.ComplexAnalysis
