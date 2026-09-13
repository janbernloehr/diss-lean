import NLS.ComplexAnalysis.LogDerivativeLocal
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Scalar analytic zero counts on compact connected sets

The count sums natural analytic orders. On a compact connected set carrying
a nonzero analytic function, the zeros are finite and all analytic orders
are finite, so this is the actual sum of multiplicities.
-/

noncomputable section
open Filter Topology
open scoped Classical
namespace NLS.ComplexAnalysis

/-- Sum the natural analytic multiplicities in the specified set. -/
def analyticZeroCount (f : ℂ → ℂ) (K : Set ℂ) : ℕ :=
  ∑ᶠ z : ℂ, if z ∈ K then analyticOrderNatAt f z else 0

/-- A nonzero analytic function has only finitely many zeros in a compact connected set. -/
theorem finite_analytic_zeros {f : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hconn : IsConnected K) (hf : AnalyticOnNhd ℂ f K)
    {b : ℂ} (hb : b ∈ K) (hfb : f b ≠ 0) : (K ∩ f ⁻¹' {0}).Finite := by
  have h := hK.finite_sdiff_of_mem_codiscreteWithin (hf.preimage_zero_mem_codiscreteWithin hfb hb hconn)
  simpa only [Set.sdiff_eq, Set.preimage_compl, compl_compl] using h

/-- Nontriviality at one point excludes infinite analytic order everywhere in the connected set. -/
theorem analyticOrderAt_ne_top_on_connected {f : ℂ → ℂ} {K : Set ℂ}
    (hconn : IsPreconnected K) (hf : AnalyticOnNhd ℂ f K)
    {b : ℂ} (hb : b ∈ K) (hfb : f b ≠ 0) {z : ℂ} (hz : z ∈ K) :
    analyticOrderAt f z ≠ ⊤ := by
  intro htop
  have he : f =ᶠ[𝓝 z] 0 := analyticOrderAt_eq_top.mp htop
  exact hfb (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz he hb)

/-- The support of the counting function lies in the actual zero set. -/
theorem analyticZeroCount_support_subset (f : ℂ → ℂ) (K : Set ℂ) :
    Function.support (fun z : ℂ => if z ∈ K then analyticOrderNatAt f z else 0) ⊆ K ∩ f ⁻¹' {0} := by
  intro z hz
  by_cases hzk : z ∈ K
  · refine ⟨hzk, ?_⟩
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero (by simpa [Function.mem_support, hzk] using hz)
  · simp [Function.mem_support, hzk] at hz

/-- Any finite set of points in `K` covering its zeros computes the exact natural count. -/
theorem analyticZeroCount_eq_sum {f : ℂ → ℂ} {K : Set ℂ} (s : Finset ℂ)
    (hs : (s : Set ℂ) ⊆ K) (hcover : K ∩ f ⁻¹' {0} ⊆ s) :
    analyticZeroCount f K = ∑ z ∈ s, analyticOrderNatAt f z := by
  unfold analyticZeroCount
  rw [finsum_eq_sum_of_support_subset _ ((analyticZeroCount_support_subset f K).trans hcover)]
  exact Finset.sum_congr rfl (fun z hz => if_pos (hs hz))

/-- A nonzero analytic function on a compact connected set has a genuine finite-support count. -/
theorem analyticZeroCount_hasFiniteSupport {f : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hconn : IsConnected K) (hf : AnalyticOnNhd ℂ f K)
    {b : ℂ} (hb : b ∈ K) (hfb : f b ≠ 0) :
    (fun z : ℂ => if z ∈ K then analyticOrderNatAt f z else 0).HasFiniteSupport :=
  (finite_analytic_zeros hK hconn hf hb hfb).subset (analyticZeroCount_support_subset f K)

end NLS.ComplexAnalysis
