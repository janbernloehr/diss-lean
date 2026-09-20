import NLS.ZakharovShabat.CanonicalPeriodicEndpoints

/-!
# Central region bounds for periodic endpoint labels

Real-part separation detects central indices even when the imaginary part
is unrestricted. The central box also gives a uniform compact bound.
-/

noncomputable section
open Set Complex Metric
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ}

/-- An endpoint with real part inside the closed central bounds has a central index. -/
theorem PeriodicEndpointLabeling.index_le_of_abs_re_le (h : PeriodicEndpointLabeling hp φ N ξ η)
    (n : ℤ) (z : ℂ) (hz : ξ n = z ∨ η n = z) (hr : |z.re| ≤ centralCircleRadius N) :
    n.natAbs ≤ N := by
  by_contra hn
  have hd := abs_lt.mp (h.abs_re_distant_sub_lt n (by omega) z hz)
  have hb := abs_le.mp hr
  unfold centralCircleRadius at hb
  by_cases hsign : 0 ≤ n
  · have hc : (N : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast (show (N : ℤ)+1 ≤ n by omega)
    nlinarith [Real.pi_pos]
  · have hc : (n : ℝ) ≤ -(N : ℝ)-1 := by exact_mod_cast (show n ≤ -(N : ℤ)-1 by omega)
    nlinarith [Real.pi_pos]

/-- All spectral points in the closed central vertical strip belong to the finite central spectrum. -/
theorem PeriodicEndpointLabeling.spectrum_mem_central_of_abs_re_le
    (h : PeriodicEndpointLabeling hp φ N ξ η) (z : ℂ)
    (hz : z ∈ periodicSpectrum hp φ) (hr : |z.re| ≤ centralCircleRadius N) :
    z ∈ centralPeriodicSpectrum hp φ N := by
  obtain ⟨n,hn⟩ := (h.exhaustive z).mp hz
  exact (h.central.root_iff z).mp ⟨n,h.index_le_of_abs_re_le n z hn hr,hn⟩

/-- Central endpoints lie in one compact ball whose radius depends only on the cutoff. -/
theorem PeriodicEndpointLabeling.norm_central_le (h : PeriodicEndpointLabeling hp φ N ξ η)
    (n : ℤ) (hn : n.natAbs ≤ N) (z : ℂ) (hz : ξ n = z ∨ η n = z) :
    ‖z‖ ≤ centralCircleRadius N + N := by
  have hm := (h.central.root_iff z).mp ⟨n,hn,hz⟩
  have hb := ((mem_centralPeriodicSpectrum hp φ N z).mp hm).2
  exact (norm_le_abs_re_add_abs_im z).trans (add_le_add hb.1.le hb.2)

end NLS.ZakharovShabat
