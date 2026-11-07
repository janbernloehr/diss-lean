import NLS.ComplexAnalysis.EvenEntireCircleGrowth
import NLS.ComplexAnalysis.SimpleZeroQuotient
import NLS.ComplexAnalysis.AnalyticScalarFactorUniqueness

/-! Odd entire interpolation with a subquadratic quotient determines
a nonzero scalar factor. Simple denominator zeros are filled before
parity and growth are used, so the factorization holds at every zero. -/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem entire_factor_even_of_odd (f g Q : ℂ → ℂ)
    (hg : AnalyticOnNhd ℂ g univ) (hQ : AnalyticOnNhd ℂ Q univ) (hgne : g ≠ 0)
    (hfodd : ∀ z : ℂ, f (-z) = -f z) (hgodd : ∀ z : ℂ, g (-z) = -g z)
    (hfactor : ∀ z : ℂ, Q z*g z = f z) : ∀ z : ℂ, Q (-z) = Q z := by
  have hQneg : AnalyticOnNhd ℂ (fun z : ℂ => Q (-z)) univ := fun z _ =>
    (hQ (-z) (mem_univ _)).comp (f := fun w : ℂ => -w) analyticAt_id.neg
  have hwitness : ∃ a ∈ (univ : Set ℂ), g a ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hgne (funext (fun z => hn z (mem_univ _)))
  have heq : EqOn (fun z : ℂ => Q (-z)) Q univ :=
    analytic_eqOn_of_mul_eq_mul_on_open isPreconnected_univ isOpen_univ Subset.rfl
      g (fun z : ℂ => Q (-z)) Q hg hQneg hQ hwitness (by
        intro z _
        calc
          g z*Q (-z) = -(Q (-z)*g (-z)) := by rw [hgodd]; ring
          _ = -f (-z) := by rw [hfactor]
          _ = f z := by rw [hfodd,neg_neg]
          _ = g z*Q z := by rw [← hfactor]; ring)
  exact fun z => heq (mem_univ z)

theorem exists_nonzero_const_factor_of_odd_simple_interpolation
    (f g : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f univ) (hg : AnalyticOnNhd ℂ g univ)
    (hfne : f ≠ 0) (hgne : g ≠ 0)
    (hfodd : ∀ z : ℂ, f (-z) = -f z) (hgodd : ∀ z : ℂ, g (-z) = -g z)
    (hcommon : ∀ z : ℂ, g z = 0 → f z = 0) (hsimple : ∀ z : ℂ, g z = 0 → deriv g z ≠ 0)
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop)
    (hGcircle : ∀ᶠ k : ℕ in atTop, ∀ z ∈ sphere (0:ℂ) (R k), g z ≠ 0)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      ∀ z ∈ sphere (0:ℂ) (R k), ‖f z/g z‖ ≤ ε*(R k)^2) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ z : ℂ, f z = C*g z := by
  let Q := analyticQuotient f g
  have hQ : AnalyticOnNhd ℂ Q univ :=
    analyticOnNhd_analyticQuotient_of_simple_zeros hf hg hcommon hsimple
  have hfactor : ∀ z : ℂ, Q z*g z = f z := analyticQuotient_mul_of_simple_zeros hf hg hcommon
  have heven := entire_factor_even_of_odd f g Q hg hQ hgne hfodd hgodd hfactor
  have hconst : ∀ z : ℂ, Q z = Q 0 := by
    apply entire_even_eq_const_of_subquadratic_circles Q hQ heven R hR
    intro ε hε
    filter_upwards [hsmall ε hε,hGcircle] with k hk hG z hz
    rw [show Q z = f z/g z from analyticQuotient_eq_div hf hg z (hG z hz)]
    exact hk z hz
  refine ⟨Q 0,?_,?_⟩
  · intro hc
    apply hfne
    funext z
    change f z = 0
    rw [← hfactor z,hconst z,hc,zero_mul]
  · intro z
    rw [← hfactor z,hconst z]

end NLS.ComplexAnalysis
