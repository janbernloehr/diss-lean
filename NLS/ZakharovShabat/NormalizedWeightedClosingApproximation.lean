import NLS.ZakharovShabat.NormalizedWeightedClosingTargets
import NLS.ZakharovShabat.NormalizedWeightedClosingInverseReality

/-! # Approximation by real sources with distant closing equations zero

Truncated normalized targets have real inverse sources arbitrarily close
in the full weighted norm. Positivity of the weight turns zero weighted
coordinates into zero actual spectral closing equations.
-/

noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Arbitrarily near each real source there is a real source solving
all sufficiently distant actual closing equations simultaneously. -/
theorem exists_real_normalizedWeightedClosingApproximation
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) (φ : CoeffPair p)
    (hreal : IsRealType (CoeffPair.toMax p φ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ ψ : CoeffPair p,
      IsRealType (CoeffPair.toMax p ψ) ∧ ‖ψ-φ‖ < ε ∧
      normalizedWeightedClosingMap hp w ψ N = sourceSymmetricTruncate (N-1) φ ∧
      ∀ n : ℤ, N ≤ n.natAbs →
        let ζ := weightedResonantDiagonalCenter hp w (normalizedWeightedPeriodOne w ψ) n;
        weightedResonantBMinusExtension hp w (normalizedWeightedPeriodOne w ψ) n ζ = 0 ∧
        weightedResonantBPlusExtension hp w (normalizedWeightedPeriodOne w ψ) n ζ = 0 := by
  obtain ⟨δ,hδ,N₀,hN₀,hG⟩ := exists_uniform_real_normalizedWeightedClosingInverse hp hp1 w φ hreal
  have hball := eventually_normalizedWeightedClosingTarget_mem_ball hp hp1 w φ δ hδ
  have hsmall : ∀ᶠ N : ℕ in atTop,
      ‖sourceSymmetricTruncate N φ-normalizedWeightedClosingMap hp w φ (N+1)‖ < ε/2 := by
    have h := (tendsto_normalizedWeightedClosingTarget_difference hp hp1 w φ).eventually
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
    have hw : (w (2*n) : ℂ) ≠ 0 := w.toWeight.complex_ne_zero _
    exact ⟨(mul_eq_zero.mp (hc.1.trans hz.1)).resolve_left hw,
      (mul_eq_zero.mp (hc.2.trans hz.2)).resolve_left hw⟩

end NLS.ZakharovShabat
