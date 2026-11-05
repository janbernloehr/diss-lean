import NLS.ComplexAnalysis.ShiftedSquareRootBounds
import NLS.ComplexAnalysis.RealCutConjugation
import Mathlib.Analysis.Complex.SqrtDeriv

/-! # Boundary limits of the physical sign of a square root

Strict real-part signs select the principal square root, or its negative.
A continuous filled square that is nonnegative real at the boundary then
supplies the full one-sided limits, including a zero boundary value.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ComplexConjugate
namespace NLS.ComplexAnalysis

theorem eq_sqrt_of_sq_re_pos {u v : ℂ} (hsq : u^2 = v) (hre : 0 < u.re) : u = sqrt v := by
  rcases eq_or_eq_neg_of_sq_eq_sq u (sqrt v) (hsq.trans (complex_sqrt_sq v).symm) with h | h
  · exact h
  · have hp := re_sqrt_nonneg v
    have he := congrArg Complex.re h
    simp only [neg_re] at he
    linarith

theorem eq_neg_sqrt_of_sq_re_neg {u v : ℂ} (hsq : u^2 = v) (hre : u.re < 0) : u = -sqrt v := by
  have hh := eq_sqrt_of_sq_re_pos (u := -u) (v := v) (by simpa only [neg_sq] using hsq)
    (by simpa only [neg_re] using neg_pos.mpr hre)
  simpa only [neg_neg] using congrArg Neg.neg hh

theorem tendsto_sqrt_of_sq_re_pos {A : Type*} {l : Filter A}
    (f g : A → ℂ) (v : ℂ) (hv : 0 ≤ v.re) (hg : Tendsto g l (𝓝 v))
    (hsq : ∀ᶠ a in l, f a^2 = g a) (hre : ∀ᶠ a in l, 0 < (f a).re) :
    Tendsto f l (𝓝 (sqrt v)) := by
  apply ((continuousAt_sqrt (Or.inl hv)).tendsto.comp hg).congr'
  filter_upwards [hsq,hre] with a ha hr
  exact (eq_sqrt_of_sq_re_pos ha hr).symm

theorem tendsto_neg_sqrt_of_sq_re_neg {A : Type*} {l : Filter A}
    (f g : A → ℂ) (v : ℂ) (hv : 0 ≤ v.re) (hg : Tendsto g l (𝓝 v))
    (hsq : ∀ᶠ a in l, f a^2 = g a) (hre : ∀ᶠ a in l, (f a).re < 0) :
    Tendsto f l (𝓝 (-sqrt v)) := by
  apply ((continuousAt_sqrt (Or.inl hv)).tendsto.comp hg).neg.congr'
  filter_upwards [hsq,hre] with a ha hr
  exact (eq_neg_sqrt_of_sq_re_neg ha hr).symm

/-- Reflection on the upper side determines the real boundary value of
any continuous filled square. -/
theorem im_eq_zero_of_continuous_reflection_upper (g : ℂ → ℂ) (x : ℝ)
    (hg : ContinuousAt g (x : ℂ))
    (he : ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] (x : ℂ), g (conj z) = conj (g z)) :
    (g x).im = 0 := by
  have hmem : (x : ℂ) ∈ closure {z : ℂ | 0 < z.im} := by
    simp only [closure_setOfPred_lt_im,mem_ofPred_eq,ofReal_im,le_refl]
  let : NeBot (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) :=
    mem_closure_iff_nhdsWithin_neBot.mp hmem
  have hc : Tendsto (fun z : ℂ => conj z)
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (x : ℂ)) := by
    have hh : ContinuousAt (fun z : ℂ => conj z) (x : ℂ) := by fun_prop
    simpa only [conj_ofReal] using hh.tendsto.mono_left nhdsWithin_le_nhds
  have hleft : Tendsto (fun z : ℂ => g (conj z))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (g x)) := hg.tendsto.comp hc
  have hright : Tendsto (fun z : ℂ => conj (g z))
      (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (conj (g x))) :=
    (hg.tendsto.mono_left nhdsWithin_le_nhds).star
  have hh := congrArg Complex.im (tendsto_nhds_unique (hleft.congr' he) hright)
  simp only [conj_im] at hh
  linarith

end NLS.ComplexAnalysis
