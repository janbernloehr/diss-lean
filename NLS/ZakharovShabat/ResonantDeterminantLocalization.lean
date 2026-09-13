import NLS.ZakharovShabat.ResonantCoefficientSmallness
import NLS.ZakharovShabat.ResonantDeterminantBounds

/-!
# Uniform localization of the actual analytic determinant

The small coefficient bounds, analyticity, and original matrix agreement
hold on one neighborhood and all distant strips. Every scalar zero lies
in the refined disc, and the strict quadratic comparison holds on its
boundary. A count of analytic zeros with multiplicity is a separate step.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Uniform analytic-domain control and numerical coefficient bounds share one threshold. -/
theorem exists_uniform_resonantDeterminant_control (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ n : ℤ, N ≤ n.natAbs →
        U ×ˢ resonantStrip n ⊆ weightedCorrectionDomain hp w n ∧
        ∀ ψ ∈ U, ∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
          ‖weightedPotentialSquareInShift hp w ψ n z hz‖ ≤ 1/2 ∧
          ‖weightedResonantAExtension hp w ψ n z‖ ≤ Real.pi/32 ∧
          ‖weightedResonantBMinusExtension hp w ψ n z‖ ≤ Real.pi/16 ∧
          ‖weightedResonantBPlusExtension hp w ψ n z‖ ≤ Real.pi/16 := by
  obtain ⟨N₁,hN₁,U₁,ho₁,hc₁,hφ₁,h0₁,h₁⟩ := exists_uniform_resonantCoefficients_pi_bounds hp hp1 w φ
  obtain ⟨N₂,_,U₂,ho₂,hc₂,hφ₂,h0₂,_,h₂⟩ := exists_uniform_complementarySquare_half hp w φ
  refine ⟨max N₁ N₂, hN₁.trans (le_max_left _ _), U₁ ∩ U₂,
    ho₁.inter ho₂, hc₁.inter hc₂, ⟨hφ₁,hφ₂⟩, ⟨h0₁,h0₂⟩, ?_⟩
  intro n hn
  refine ⟨?_, ?_⟩
  · intro s hs
    exact mem_weightedCorrectionDomain hp w s.1 n s.2 hs.2
      ((h₂ s.1 hs.1.2 n (by omega) s.2 hs.2).1.trans_lt (by norm_num))
  · intro ψ hψ z hz
    exact ⟨(h₂ ψ hψ.2 n (by omega) z hz).1, h₁ ψ hψ.1 n (by omega) z hz⟩

/-- Lemma 6.9's localization and strict boundary comparison for the actual determinant, locally uniformly. -/
theorem exists_uniform_resonantDeterminant_localization (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        AnalyticOnNhd ℂ (resonantDeterminantExtension hp w ψ n) (resonantStrip n) ∧
        (∀ z : ℂ, ∀ hz : z ∈ resonantStrip n,
          ∃ h : ‖weightedPotentialSquareInShift hp w ψ n z hz‖ < 1,
            resonantDeterminantExtension hp w ψ n z = (weightedResonantMatrix hp w ψ n z hz h).det) ∧
        (∀ z ∈ resonantStrip n, resonantDeterminantExtension hp w ψ n z = 0 →
          ‖z - (Real.pi : ℂ)*n‖ ≤ 3*Real.pi/32 ∧ z ∈ refinedResonantDisk n) ∧
        (∀ z ∈ Metric.sphere ((Real.pi : ℂ)*n) (Real.pi/4),
          ‖resonantDeterminantExtension hp w ψ n z - (z - (Real.pi : ℂ)*n)^2‖ <
            ‖(z - (Real.pi : ℂ)*n)^2‖) := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hb⟩ := exists_uniform_resonantDeterminant_control hp hp1 w φ
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ n hn
  have hdom (z : ℂ) (hz : z ∈ resonantStrip n) : (ψ,z) ∈ weightedCorrectionDomain hp w n :=
    (hb n hn).1 ⟨hψ,hz⟩
  have hbounds (z : ℂ) (hz : z ∈ resonantStrip n) := (hb n hn).2 ψ hψ z hz
  refine ⟨fun z hz => analyticAt_resonantDeterminantExtension_spectral hp w ψ n z (hdom z hz), ?_, ?_, ?_⟩
  · intro z hz
    have h := (hbounds z hz).1.trans_lt (by norm_num : (1/2 : ℝ) < 1)
    exact ⟨h, resonantDeterminantExtension_eq_det hp w ψ n z hz h⟩
  · intro z hz hzero
    have h := norm_resonant_quadratic_root_le (z - (Real.pi : ℂ)*n)
      (weightedResonantAExtension hp w ψ n z) (weightedResonantBPlusExtension hp w ψ n z)
      (weightedResonantBMinusExtension hp w ψ n z) (hbounds z hz).2.1
      (hbounds z hz).2.2.2 (hbounds z hz).2.2.1 hzero
    refine ⟨h, ?_⟩
    change dist z ((Real.pi : ℂ)*n) < Real.pi/4
    rw [dist_eq_norm]
    exact h.trans_lt (by linarith [Real.pi_pos])
  · intro z hz
    have hzstrip : z ∈ resonantStrip n :=
      closedBall_subset_resonantStrip n (by linarith [Real.pi_pos]) (Metric.sphere_subset_closedBall hz)
    have hq : ‖z - (Real.pi : ℂ)*n‖ = Real.pi/4 := by simpa only [dist_eq_norm] using Metric.mem_sphere.mp hz
    exact norm_resonant_quadratic_error_lt _ _ _ _ hq (hbounds z hzstrip).2.1
      (hbounds z hzstrip).2.2.2 (hbounds z hzstrip).2.2.1

end NLS.ZakharovShabat
