import NLS.ZakharovShabat.WeightedResonantCenterRemainderDerivative
import NLS.ZakharovShabat.WeightedResonantCenterClosingTail

/-!
# Derivative control of the actual spectral closing map

The derivative of the full closing map differs from its signed weighted
Fourier leading map by the derivative of the actual remainder. One fixed
source ball makes this difference arbitrarily small, for every larger
cutoff, and supplies an explicit Lipschitz bound for the full derivative.
Every tail coordinate retains the actual off-diagonal closing equation.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The derivative of the actual closing map is the leading Fourier
operator plus the actual remainder derivative. -/
theorem fderiv_weightedResonantCenterClosingTail (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ)
    (hR : DifferentiableAt ℂ (fun ψ => weightedResonantCenterRemainder hp w ψ N) φ) :
    fderiv ℂ (fun ψ => weightedResonantCenterClosingTail hp w ψ N) φ =
      weightedResonantLeadingTailCLM hp w N+
        fderiv ℂ (fun ψ => weightedResonantCenterRemainder hp w ψ N) φ :=
  ((weightedResonantLeadingTailCLM hp w N).hasFDerivAt.add hR.hasFDerivAt).fderiv

/-- The full actual closing map has a derivative uniformly close to
the leading Fourier operator on a fixed ball, together with a Lipschitz
derivative bound. Membership and the exact actual coefficients are
constructed throughout the outer ball. -/
theorem exists_fixedBall_weightedResonantCenterClosingTail_derivative
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (η : ℝ) (hη : 0 < η) :
    let K := resonantCenterRemainderBallConstant p (‖φ‖+1);
    ∃ r : ℝ, 0 < r ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      AnalyticOnNhd ℂ (fun ψ => weightedResonantCenterClosingTail hp w ψ N) (ball φ (4*r)) ∧
      (∀ ψ ∈ ball φ (4*r),
        ‖weightedResonantCenterClosingTail hp w ψ N-weightedResonantLeadingTailCLM hp w N ψ‖ ≤ K*r^2 ∧
        ∀ n : ℤ,
          ((weightedResonantCenterClosingTail hp w ψ N).fst n =
            if N ≤ n.natAbs then (w (2*n) : ℂ)*weightedResonantBMinusExtension hp w ψ n
              (weightedResonantDiagonalCenter hp w ψ n) else 0) ∧
          ((weightedResonantCenterClosingTail hp w ψ N).snd n =
            if N ≤ n.natAbs then (w (2*n) : ℂ)*weightedResonantBPlusExtension hp w ψ n
              (weightedResonantDiagonalCenter hp w ψ n) else 0)) ∧
      (∀ ψ ∈ ball φ (3*r),
        ‖fderiv ℂ (fun χ => weightedResonantCenterClosingTail hp w χ N) ψ-
          weightedResonantLeadingTailCLM hp w N‖ < η) ∧
      ∀ x ∈ ball φ r, ∀ y ∈ ball φ r,
        ‖fderiv ℂ (fun χ => weightedResonantCenterClosingTail hp w χ N) y-
          fderiv ℂ (fun χ => weightedResonantCenterClosingTail hp w χ N) x‖ ≤ 4*K*‖y-x‖ := by
  obtain ⟨r,hr,N₀,hN₀,hR⟩ :=
    exists_fixedBall_weightedResonantCenterRemainder_derivative hp hp1 w φ η hη
  refine ⟨r,hr,N₀,hN₀,?_⟩
  intro N hN
  have h := hR N hN
  have hinner : ball φ (3*r) ⊆ ball φ (4*r) := ball_subset_ball (by linarith)
  have hsmall : ball φ r ⊆ ball φ (4*r) := ball_subset_ball (by linarith)
  have hder (ψ : WeightedCoeffPair w.toWeight p) (hψ : ψ ∈ ball φ (4*r)) :=
    fderiv_weightedResonantCenterClosingTail hp w ψ N (h.1 ψ hψ).differentiableAt
  refine ⟨?_,?_,?_,?_⟩
  · intro ψ hψ
    exact ((weightedResonantLeadingTailCLM hp w N).analyticAt ψ).add (h.1 ψ hψ)
  · intro ψ hψ
    rw [weightedResonantCenterClosingTail_sub_leading]
    exact ⟨(h.2.1 ψ hψ).2,weightedResonantCenterClosingTail_apply_of_mem hp w ψ N (h.2.1 ψ hψ).1⟩
  · intro ψ hψ
    rw [hder ψ (hinner hψ),add_sub_cancel_left]
    exact h.2.2.1 ψ hψ
  · intro x hx y hy
    rw [hder y (hsmall hy),hder x (hsmall hx),add_sub_add_left_eq_sub]
    exact h.2.2.2.2 x hx y hy

end NLS.ZakharovShabat
