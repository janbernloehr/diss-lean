import NLS.ZakharovShabat.SourceClosingTargets
import NLS.ZakharovShabat.SourceAdaptedClosingInverseReality

/-!
# Nearby real sources solving every distant closing equation

Symmetric truncations eventually lie in the common inverse image
balls. Their inverse sources preserve real type and approach the
original source in its full pair norm. Every high target coefficient
is zero, so every corresponding actual spectral closing equation
vanishes, with the original periodic spectrum and determinant order
given by the proved moving-center criterion.
-/

noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Arbitrarily near each real source there is a real source solving
all sufficiently distant actual closing equations simultaneously. -/
theorem exists_real_sourceClosingApproximation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ ψ : CoeffPair p,
      IsRealType (CoeffPair.toMax p ψ) ∧ ‖ψ-φ‖ < ε ∧
      sourceAdaptedClosingMap hp ψ N = sourceSymmetricTruncate (N-1) φ ∧
      ∀ n : ℤ, N ≤ n.natAbs →
        let ζ := weightedResonantDiagonalCenter hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n;
        weightedResonantBMinusExtension hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n ζ = 0 ∧
        weightedResonantBPlusExtension hp SpectralWeight.one (sourceWeightedPeriodOne ψ) n ζ = 0 ∧
        (∀ z ∈ resonantStrip n, z ∈ periodicSpectrum hp (periodOnePotential ψ) ↔ z = ζ) ∧
        ∀ z ∈ resonantStrip n,
          analyticOrderNatAt (resonantDeterminantExtension hp SpectralWeight.one
            (sourceWeightedPeriodOne ψ) n) z = if z = ζ then 2 else 0 := by
  obtain ⟨δ,hδ,N₀,hN₀,hG⟩ := exists_uniform_real_sourceAdaptedClosingInverse hp hp1 φ hreal
  have hball := eventually_sourceClosingTarget_mem_ball hp hp1 φ δ hδ
  have hsmall : ∀ᶠ N : ℕ in atTop,
      ‖sourceSymmetricTruncate N φ-sourceAdaptedClosingMap hp φ (N+1)‖ < ε/2 := by
    have h := (tendsto_sourceClosingTarget_difference hp hp1 φ).eventually
      (ball_mem_nhds 0 (show 0 < ε/2 by positivity))
    simpa only [mem_ball,dist_zero_right] using h
  obtain ⟨M,hM,hballM,hsmallM⟩ :=
    ((eventually_ge_atTop N₀).and (hball.and hsmall)).exists
  obtain ⟨g,_,_,hdata⟩ := hG (M+1) (by omega)
  have hi := hdata (sourceSymmetricTruncate M φ) hballM
  refine ⟨M+1,by omega,g (sourceSymmetricTruncate M φ),
    hi.2.2.1 (sourceSymmetricTruncate_realType M φ hreal),?_,?_,?_⟩
  · have hb := hi.2.1
    linarith
  · simpa only [Nat.add_sub_cancel] using hi.1
  · intro n hn
    have hz := sourceSymmetricTruncate_high M φ n hn
    have hc := hi.2.2.2 n hn
    exact ⟨hc.1.1.trans hz.1,hc.1.2.trans hz.2,hc.2 hz.1 hz.2⟩

end NLS.ZakharovShabat
