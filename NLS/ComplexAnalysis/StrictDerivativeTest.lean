import Mathlib.Analysis.Calculus.DerivativeTest

/-!
# Strict second-derivative tests on the real line

A nonzero second derivative at a critical point fixes the nearby derivative
sign. Strict monotonicity on the two adjacent half intervals gives a strict
local extremum, expressed on a punctured neighborhood.
-/

open Set Filter Topology Metric
namespace NLS.ComplexAnalysis

/-- A positive second derivative at a critical point gives a strict local minimum. -/
theorem eventually_lt_of_deriv_deriv_pos {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ}
    (hzero : deriv f c = 0) (hpos : 0 < deriv (deriv f) c) :
    ∀ᶠ x in 𝓝[≠] c, f c < f x := by
  have hs := eventually_nhdsWithin_sign_eq_of_deriv_pos hpos hzero
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hs
  have hl : StrictAntiOn f (Icc (c-ε) c) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hf.continuousOn
    intro x hx
    have hx' : c-ε < x ∧ x < c := by simpa only [interior_Icc,mem_Ioo] using hx
    have hb : x ∈ ball c ε := by
      rw [mem_ball,Real.dist_eq,abs_lt]
      constructor <;> linarith
    exact sign_eq_neg_one_iff.mp ((hball hb).trans (sign_neg (by linarith)))
  have hr : StrictMonoOn f (Icc c (c+ε)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hf.continuousOn
    intro x hx
    have hx' : c < x ∧ x < c+ε := by simpa only [interior_Icc,mem_Ioo] using hx
    have hb : x ∈ ball c ε := by
      rw [mem_ball,Real.dist_eq,abs_lt]
      constructor <;> linarith
    exact sign_eq_one_iff.mp ((hball hb).trans (sign_pos (by linarith)))
  have hn : Ioo (c-ε) (c+ε) ∈ 𝓝 c := Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [nhdsWithin_le_nhds hn,self_mem_nhdsWithin] with x hx hxc
  have hne : x ≠ c := by simpa using hxc
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hl ⟨hx.1.le,hlt.le⟩ ⟨by linarith,le_rfl⟩ hlt
  · exact hr ⟨le_rfl,by linarith⟩ ⟨hgt.le,hx.2.le⟩ hgt

/-- A negative second derivative at a critical point gives a strict local maximum. -/
theorem eventually_lt_of_deriv_deriv_neg {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ}
    (hzero : deriv f c = 0) (hneg : deriv (deriv f) c < 0) :
    ∀ᶠ x in 𝓝[≠] c, f x < f c := by
  have hn : deriv (-f) = -(deriv f) := funext (fun _ => deriv.neg)
  have he := eventually_lt_of_deriv_deriv_pos (f := -f) (c := c) hf.neg
    (by rw [deriv.neg,hzero,neg_zero])
    (by rw [hn,deriv.neg]; exact neg_pos.mpr hneg)
  simpa only [Pi.neg_apply,neg_lt_neg_iff] using he

/-- A critical point with nonzero second derivative is a strict local minimum or maximum. -/
theorem strict_local_extremum_of_second_derivative_ne_zero {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ}
    (hzero : deriv f c = 0) (hne : deriv (deriv f) c ≠ 0) :
    (∀ᶠ x in 𝓝[≠] c, f c < f x) ∨ (∀ᶠ x in 𝓝[≠] c, f x < f c) := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact Or.inr (eventually_lt_of_deriv_deriv_neg hf hzero hneg)
  · exact Or.inl (eventually_lt_of_deriv_deriv_pos hf hzero hpos)

/-- A punctured strict local minimum or maximum is also a local extremum in the standard sense. -/
theorem isLocalExtr_of_strict_punctured {f : ℝ → ℝ} {c : ℝ}
    (h : (∀ᶠ x in 𝓝[≠] c, f c < f x) ∨ (∀ᶠ x in 𝓝[≠] c, f x < f c)) :
    IsLocalExtr f c := by
  rcases h with hmin | hmax
  · left
    change ∀ᶠ x in 𝓝 c, f c ≤ f x
    rw [← nhdsNE_sup_pure c, eventually_sup]
    exact ⟨hmin.mono (fun _ hx => hx.le),by simp⟩
  · right
    change ∀ᶠ x in 𝓝 c, f x ≤ f c
    rw [← nhdsNE_sup_pure c, eventually_sup]
    exact ⟨hmax.mono (fun _ hx => hx.le),by simp⟩

end NLS.ComplexAnalysis
