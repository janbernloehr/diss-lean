import NLS.KdV.HillHminusOneActionRatio
import NLS.ComplexAnalysis.DenseSegmentComplement
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! # Actual local high Hill action charts

A chart retains the actual multiplicity-counted spectral pair, analytic
filled square, trace, intrinsic normalized root and its fixed near-one
normalization. The predicate contains no supplied action or action ratio.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

def HillHminusActionChartValid (n : ℕ+) (r : ℝ) (K : ℂ × PeriodOneHminusOne → ℂ)
    (q : PeriodOneHminusOne) : Prop :=
  0 < r ∧
  AnalyticOnNhd ℂ (fun z => K (z,q))
    (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)) ∧
  AnalyticOnNhd ℂ (fun z => hillHminusJointNormalizedGapRoot n r K (z,q))
    (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r)) ∧
  (∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
    squaredCosh (K (z,q)) = (-1 : ℂ)^(n : ℕ)*hillHminusDiscriminant q z/2) ∧
  (∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
    K (z,q) = -hillHminusGapPolynomial n r (z,q)*hillHminusJointNormalizedGapRoot n r K (z,q)^2 /
      (4*((Real.pi : ℂ)*(n : ℕ))^2)) ∧
  (∀ z ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r),
    ‖hillHminusJointNormalizedGapRoot n r K (z,q)-1‖ < 1) ∧
  ∃ l u : ℂ, HillHminusHighGapPair q n r l u

theorem HillHminusHighGapPair.align_other_radius
    {q : PeriodOneHminusOne} {n : ℕ+} {r s : ℝ} {l u a b : ℂ}
    (h : HillHminusHighGapPair q n r l u) (k : HillHminusHighGapPair q n s a b) :
    HillHminusHighGapPair q n s l u := by
  rcases h.eq_or_swap k with ⟨hla,hub⟩ | ⟨hlb,hua⟩
  · rw [hla,hub]
    exact k
  · rw [hlb,hua]
    exact k.swap

theorem HillHminusHighGapPair.gapPolynomial_eq_other_radius
    {q : PeriodOneHminusOne} {n : ℕ+} {r s : ℝ} {l u a b : ℂ}
    (h : HillHminusHighGapPair q n r l u) (k : HillHminusHighGapPair q n s a b)
    (hr : 0 < r) (hs : 0 < s) (z : ℂ) :
    hillHminusGapPolynomial n r (z,q) = hillHminusGapPolynomial n s (z,q) := by
  rw [h.gapPolynomial_eq hr z,(h.align_other_radius k).gapPolynomial_eq hs z]

theorem eqOn_of_squaredCosh_eq_at_common_zero
    (K L : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hc : IsPreconnected U)
    (hK : AnalyticOnNhd ℂ K U) (hL : AnalyticOnNhd ℂ L U)
    (p : ℂ) (hp : p ∈ U) (hK0 : K p = 0) (hL0 : L p = 0)
    (he : ∀ z ∈ U, squaredCosh (K z) = squaredCosh (L z)) : EqOn K L U := by
  have hnear : (fun z => squaredCosh (K z)) =ᶠ[𝓝 p] (fun z => squaredCosh (L z)) :=
    Filter.eventually_of_mem (hU.mem_nhds hp) (fun z hz => he z hz)
  exact hK.eqOn_of_preconnected_of_eventuallyEq hL hc hp
    (eventuallyEq_of_squaredCosh_eq K L p (hK p hp).continuousAt (hL p hp).continuousAt hK0 hL0 hnear)

theorem HillHminusActionChartValid.square_eq_on_overlap
    {q : PeriodOneHminusOne} {n : ℕ+} {r s : ℝ} {K L : ℂ × PeriodOneHminusOne → ℂ}
    (h : HillHminusActionChartValid n r K q) (k : HillHminusActionChartValid n s L q) :
    EqOn (fun z => K (z,q)) (fun z => L (z,q))
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ∩
        ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*s)) := by
  obtain ⟨l,u,hpair⟩ := h.2.2.2.2.2.2
  obtain ⟨a,b,kpair⟩ := k.2.2.2.2.2.2
  have kpair' := hpair.align_other_radius kpair
  have hzero : K (l,q) = 0 := by
    rw [h.2.2.2.2.1 l hpair.left_mem,hpair.gapPolynomial_eq h.1 l]
    simp
  have kzero : L (l,q) = 0 := by
    rw [k.2.2.2.2.1 l kpair'.left_mem,kpair'.gapPolynomial_eq k.1 l]
    simp
  apply eqOn_of_squaredCosh_eq_at_common_zero _ _ _ (isOpen_ball.inter isOpen_ball)
    ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
    (h.2.1.mono inter_subset_left) (k.2.1.mono inter_subset_right) l ⟨hpair.left_mem,kpair'.left_mem⟩ hzero kzero
  intro z hz
  rw [h.2.2.2.1 z hz.1,k.2.2.2.1 z hz.2]

end NLS.KdV
