import NLS.ComplexAnalysis.ClosedZeroPersistence

/-! # Closed constraints on parameter-zero pairs under dense approximation

The closed set may depend on the parameter. Joint closed spectral graphs
therefore contain every zero of a nontrivial entire characteristic once
this is known on a dense parameter set, including multiple zeros.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped Classical
namespace NLS.ComplexAnalysis

theorem zero_pair_mem_closed_of_closure_parameters
    {T : Type*} [PseudoMetricSpace T] (F : T → ℂ → ℂ)
    (hF : Continuous F.uncurry) (ha : ∀ t, AnalyticOnNhd ℂ (F t) univ)
    (S : Set T) (K : Set (T × ℂ)) (hK : IsClosed K)
    (hzeros : ∀ t ∈ S, ∀ z, F t z = 0 → (t,z) ∈ K)
    (t : T) (ht : t ∈ closure S) (b : ℂ) (hb : F t b ≠ 0)
    (c : ℂ) (hc : F t c = 0) : (t,c) ∈ K := by
  by_contra hcK
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp hK.isOpen_compl (t,c) hcK
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
  obtain ⟨s,hs,hsR,hscount⟩ := (hfreq.and_eventually ((show ∀ᶠ s in 𝓝 t, s ∈ ball t R from ball_mem_nhds t hR).and hstable)).exists
  have hzero : analyticZeroCount (F s) (closedBall c r) = 0 := by
    rw [analyticZeroCount_eq_sum ∅ (by simp) (by
      intro z hz
      have hzK := hzeros s hs z hz.2
      have hzball : (s,z) ∈ ball (t,c) R := by
        rw [mem_ball,Prod.dist_eq,max_lt_iff]
        exact ⟨hsR,(mem_closedBall.mp hz.1).trans_lt hrR⟩
      exact (hball hzball hzK).elim)]
    simp
  rw [hscount] at hzero
  omega


end NLS.ComplexAnalysis
