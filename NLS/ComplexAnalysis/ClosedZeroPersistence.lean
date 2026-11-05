import NLS.ComplexAnalysis.ZeroCountHomotopy
import NLS.ComplexAnalysis.ZeroMultiset

/-! # Closed spectral constraints under dense parameter limits

An entire scalar family that is jointly continuous inherits a closed
constraint on all its zeros from a dense parameter set, unless the limit
slice is identically zero. Local zero-count stability includes multiple
zeros, so no simple-root hypothesis is needed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped Classical
namespace NLS.ComplexAnalysis

/-- A constant scalar function has natural zero count zero, including
zero itself, whose analytic order is infinite rather than a finite multiplicity. -/
theorem analyticZeroCount_const (a : ℂ) (K : Set ℂ) :
    analyticZeroCount (fun _ : ℂ => a) K = 0 := by
  have ho (z : ℂ) : analyticOrderNatAt (fun _ : ℂ => a) z = 0 := by
    by_cases ha : a = 0
    · subst a
      have ht : analyticOrderAt (fun _ : ℂ => (0 : ℂ)) z = ⊤ :=
        analyticOrderAt_eq_top.mpr Filter.EventuallyEq.rfl
      simp only [analyticOrderNatAt,ht,ENat.toNat_top]
    · exact congrArg ENat.toNat (analyticOrderAt_eq_zero.mpr (Or.inr ha))
  simp only [analyticZeroCount,ho,ite_self,finsum_zero]

/-- A finite-order analytic zero is the only zero in a sufficiently small
closed disc, with any prescribed positive upper bound on its radius. -/
theorem exists_isolated_zero_disc {f : ℂ → ℂ} {c : ℂ}
    (hf : AnalyticAt ℂ f c) (hfinite : analyticOrderAt f c ≠ ⊤)
    (R : ℝ) (hR : 0 < R) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ∀ z ∈ closedBall c r, z ≠ c → f z ≠ 0 := by
  obtain ⟨g,hg,hgc,heq⟩ := hf.analyticOrderAt_ne_top.mp hfinite
  have hne : ∀ᶠ z in 𝓝 c, g z ≠ 0 := hg.continuousAt.eventually_ne hgc
  obtain ⟨d,hd,hcontrol⟩ := Metric.eventually_nhds_iff.mp (heq.and hne)
  let r : ℝ := min R d/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := by have := min_le_left R d; dsimp [r]; linarith
  have hrd : r < d := by have := min_le_right R d; dsimp [r]; linarith
  refine ⟨r,hr,hrR,?_⟩
  intro z hz hzc
  obtain ⟨he,hgne⟩ := hcontrol (hz.trans_lt hrd)
  rw [he]
  change (z-c)^analyticOrderNatAt f c*g z ≠ 0
  exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hzc)) hgne

/-- Dense parameter limits preserve every closed constraint on zeros of
a nontrivial entire family. The parameter space need only be topological. -/
theorem zero_mem_closed_of_closure_parameters
    {T : Type*} [TopologicalSpace T] (F : T → ℂ → ℂ)
    (hF : Continuous F.uncurry) (ha : ∀ t, AnalyticOnNhd ℂ (F t) univ)
    (S : Set T) (K : Set ℂ) (hK : IsClosed K)
    (hzeros : ∀ t ∈ S, ∀ z, F t z = 0 → z ∈ K)
    (t : T) (ht : t ∈ closure S) (b : ℂ) (hb : F t b ≠ 0)
    (c : ℂ) (hc : F t c = 0) : c ∈ K := by
  by_contra hcK
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp hK.isOpen_compl c hcK
  have hfinite := analyticOrderAt_ne_top_on_connected isPreconnected_univ (ha t)
    (mem_univ b) hb (mem_univ c)
  obtain ⟨r,hr,hrR,honly⟩ := exists_isolated_zero_disc (ha t c (mem_univ c)) hfinite R hR
  have hboundary : ∀ z ∈ sphere c r, F t z ≠ 0 := by
    intro z hz
    apply honly z (sphere_subset_closedBall hz)
    intro he
    have heq := mem_sphere.mp hz
    rw [he,dist_self] at heq
    linarith
  have hcount : 0 < analyticZeroCount (F t) (closedBall c r) := by
    rw [analyticZeroCount_eq_sum {c} (by simpa using (show c ∈ closedBall c r from mem_closedBall_self hr.le)) (by
      intro z hz
      have he : z = c := by by_contra h; exact honly z hz.1 h hz.2
      simpa using he)]
    simpa only [Finset.sum_singleton] using
      analyticOrderNatAt_pos_of_zero (ha t c (mem_univ c)) hfinite hc
  have hstable := eventually_analyticZeroCount_eq_of_continuous_family F c r hr
    hF.continuousOn (fun s => (ha s).mono (subset_univ _)) t hboundary
  have hfreq : ∃ᶠ s in 𝓝 t, s ∈ S := mem_closure_iff_frequently.mp ht
  obtain ⟨s,hs,hscount⟩ := (hfreq.and_eventually hstable).exists
  have hzero : analyticZeroCount (F s) (closedBall c r) = 0 := by
    rw [analyticZeroCount_eq_sum ∅ (by simp) (by
      intro z hz
      have hzK := hzeros s hs z hz.2
      have hzball : z ∈ ball c R := closedBall_subset_ball hrR hz.1
      exact (hball hzball hzK).elim)]
    simp
  rw [hscount] at hzero
  omega

end NLS.ComplexAnalysis
