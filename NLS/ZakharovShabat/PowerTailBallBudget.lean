import NLS.ZakharovShabat.UniformPowerTail

/-!
# A power-tail estimate on a fixed source ball

Choose the cutoff after choosing a positive source radius. The tail of
the center is then smaller than that radius, while the contractive
Fourier-tail operator controls perturbations throughout the same ball.
This gives one fixed-ball estimate for every larger cutoff.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On the fixed fourfold source ball, both terms in the power-tail
budget are controlled by the radius, for every sufficiently large
cutoff. No compactness of the source ball is assumed. -/
theorem exists_fixedBall_powerTail_budget (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (M r β δ : ℝ)
    (hr : 0 < r) (hβ : 0 < β) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ ψ ∈ ball φ (4*r),
        M^β/(N : ℝ)^δ + ‖weightedPairFourierTail w.toWeight (N/2) ψ‖^β ≤
          (1+5^β)*r^β := by
  have ht := (tendsto_weightedPairFourierTail hp w.toWeight φ).norm
  simp only [norm_zero] at ht
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (ht.eventually_lt_const hr)
  have hrec : Tendsto (fun N : ℕ => M^β/(N : ℝ)^δ) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop hδ).comp tendsto_natCast_atTop_atTop)
  obtain ⟨L,hL⟩ := eventually_atTop.mp
    (hrec.eventually_lt_const (Real.rpow_pos_of_pos hr β))
  refine ⟨max (2*J) (max 2 L),(le_max_left 2 L).trans (le_max_right _ _),?_⟩
  intro N hN ψ hψ
  have htailφ : ‖weightedPairFourierTail w.toWeight (N/2) φ‖ ≤ r :=
    (hJ (N/2) (by omega)).le
  have htailψ : ‖weightedPairFourierTail w.toWeight (N/2) ψ‖ ≤ 5*r := by
    have hdist : ‖ψ-φ‖ < 4*r := by simpa only [mem_ball,dist_eq_norm] using hψ
    calc
      _ ≤ ‖weightedPairFourierTail w.toWeight (N/2) (ψ-φ)‖+
          ‖weightedPairFourierTail w.toWeight (N/2) φ‖ := by
        simpa only [map_sub] using norm_le_norm_sub_add
          (weightedPairFourierTail w.toWeight (N/2) ψ) (weightedPairFourierTail w.toWeight (N/2) φ)
      _ ≤ ‖ψ-φ‖+r := add_le_add (norm_weightedPairFourierTail_le hp w.toWeight _ _) htailφ
      _ ≤ 5*r := by linarith
  calc
    _ ≤ r^β+(5*r)^β := add_le_add (hL N (by omega)).le
      (Real.rpow_le_rpow (norm_nonneg _) htailψ hβ.le)
    _ = (1+5^β)*r^β := by rw [Real.mul_rpow (by norm_num) hr.le]; ring

end NLS.ZakharovShabat
