import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! The printed Lemma A.4 assumes a small error only on the very ball
where it claims an analytic diffeomorphism. Even a scalar polynomial
can have zero derivative there. The double-ball theorem used by the
article formalization has an explicit domain margin instead. -/
noncomputable section
open Set Filter Topology Complex
namespace NLS.Articles.KdVPseudomeasures

def sourceLemmaA4Counterexample (z : ℂ) : ℂ := z-z^8/8

theorem sourceLemmaA4Counterexample_analytic :
    AnalyticOnNhd ℂ sourceLemmaA4Counterexample univ := by
  intro z _
  exact analyticAt_id.sub ((analyticAt_id.pow 8).div_const)

theorem sourceLemmaA4Counterexample_error (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖sourceLemmaA4Counterexample z-z‖ ≤ 1/8 := by
  rw [sourceLemmaA4Counterexample,sub_sub_cancel_left,norm_neg,norm_div,norm_pow]
  rw [show ‖(8:ℂ)‖=(8:ℝ) by norm_num]
  exact div_le_div_of_nonneg_right (by simpa using pow_le_pow_left₀ (norm_nonneg z) hz 8) (by norm_num)

theorem sourceLemmaA4Counterexample_hasDerivAt :
    HasDerivAt sourceLemmaA4Counterexample 0 1 := by
  have h := (hasDerivAt_id (1:ℂ)).sub (((hasDerivAt_id (1:ℂ)).pow 8).div_const 8)
  convert! h using 1; first | rfl | norm_num [sourceLemmaA4Counterexample]

theorem sourceLemmaA4Counterexample_no_analytic_inverse :
    ¬ ∃ g : ℂ → ℂ, AnalyticAt ℂ g (sourceLemmaA4Counterexample 1) ∧
      (fun z => g (sourceLemmaA4Counterexample z)) =ᶠ[𝓝 (1:ℂ)] id := by
  rintro ⟨g,hg,he⟩
  have h := hg.differentiableAt.hasDerivAt.comp 1 sourceLemmaA4Counterexample_hasDerivAt
  rw [mul_zero] at h
  have hzero : HasDerivAt (id : ℂ → ℂ) 0 1 := h.congr_of_eventuallyEq he.symm
  have hbad := hzero.unique (hasDerivAt_id (1:ℂ))
  norm_num at hbad

/-- The defect also occurs strictly inside the ball, independently of
how a diffeomorphism on the boundary of a closed ball is interpreted. -/
theorem sourceLemmaA4_interior_counterexample :
    ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f univ ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → ‖f z-z‖ ≤ 1/8) ∧
      ∃ w : ℂ, ‖w‖ < 1 ∧ HasDerivAt f 0 w ∧
        ¬ ∃ g : ℂ → ℂ, AnalyticAt ℂ g (f w) ∧ (fun z => g (f z)) =ᶠ[𝓝 w] id := by
  let f : ℂ → ℂ := fun z => z-z^16/8
  obtain ⟨w,hw⟩ := IsAlgClosed.exists_pow_nat_eq (1/2:ℂ) (by norm_num : 0 < (15:ℕ))
  have hwNorm : ‖w‖^15=(1/2:ℝ) := by
    have h := congrArg norm hw
    simpa only [norm_pow,norm_div,norm_one,show ‖(2:ℂ)‖=(2:ℝ) by norm_num] using h
  have hwlt : ‖w‖ < 1 := by
    by_contra h
    have hh := one_le_pow₀ (le_of_not_gt h) (n := 15)
    linarith
  have hd : HasDerivAt f 0 w := by
    have h := (hasDerivAt_id w).sub (((hasDerivAt_id w).pow 16).div_const 8)
    convert! h using 1; norm_num [hw]
  refine ⟨f,(fun z _ => analyticAt_id.sub ((analyticAt_id.pow 16).div_const)),?_,w,hwlt,hd,?_⟩
  · intro z hz
    change ‖(z-z^16/8)-z‖ ≤ 1/8
    rw [sub_sub_cancel_left,norm_neg,norm_div,norm_pow,show ‖(8:ℂ)‖=(8:ℝ) by norm_num]
    exact div_le_div_of_nonneg_right (by simpa using pow_le_pow_left₀ (norm_nonneg z) hz 16) (by norm_num)
  · rintro ⟨g,hg,he⟩
    have h := hg.differentiableAt.hasDerivAt.comp w hd
    rw [mul_zero] at h
    have hz : HasDerivAt (id : ℂ → ℂ) 0 w := h.congr_of_eventuallyEq he.symm
    have hb := hz.unique (hasDerivAt_id w)
    norm_num at hb

end NLS.Articles.KdVPseudomeasures
