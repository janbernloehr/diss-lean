import NLS.ZakharovShabat.WeightedResonantLeadingTail
import NLS.ZakharovShabat.WeightedResonantCenterRemainderAnalytic

/-!
# The analytic sequence map of actual spectral closing equations

Adding the signed leading Fourier tail to the actual moving-center
remainder gives an analytic map into the component-sum `ℓᵖ` pair space.
Its high coordinates are exactly the two weighted off-diagonal
coefficients at the actual diagonal centers. Vanishing coordinates
therefore close the original periodic spectrum to a double root.

For any tolerance, one open convex source neighborhood supports every
larger cutoff and bounds the joint norm difference from the leading
Fourier map. The neighborhood may depend on the tolerance; no fixed-ball
derivative bound, inverse construction, or finite-gap density is asserted.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual spectral closing tail, with the negative coefficient
in the first component and the positive coefficient in the second. -/
def weightedResonantCenterClosingTail (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) : CoeffPair p :=
  weightedResonantLeadingTailCLM hp w N φ + weightedResonantCenterRemainder hp w φ N

/-- Where membership is proved, every coordinate is exactly the
actual weighted closing equation, and the block below the cutoff is zero. -/
theorem weightedResonantCenterClosingTail_apply_of_mem
    (hp : p ≠ ⊤) (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) (N : ℕ)
    (hmem : ∀ positive : Bool,
      Memℓp (weightedResonantCenterRemainderCoordinate hp w φ N positive) p) (n : ℤ) :
    (weightedResonantCenterClosingTail hp w φ N).fst n =
      (if N ≤ n.natAbs then (w (2*n) : ℂ)*weightedResonantBMinusExtension hp w φ n
        (weightedResonantDiagonalCenter hp w φ n) else 0) ∧
    (weightedResonantCenterClosingTail hp w φ N).snd n =
      (if N ≤ n.natAbs then (w (2*n) : ℂ)*weightedResonantBPlusExtension hp w φ n
        (weightedResonantDiagonalCenter hp w φ n) else 0) := by
  have hrem := weightedResonantCenterRemainder_apply_of_mem hp w φ N hmem n
  constructor
  · change (weightedResonantLeadingTail w φ N).fst n +
      (weightedResonantCenterRemainder hp w φ N).fst n = _
    rw [weightedResonantLeadingTail_fst hp,hrem.1]
    by_cases hn : N ≤ n.natAbs <;>
      simp [weightedResonantCenterRemainderCoordinate,hn]
    ring
  · change (weightedResonantLeadingTail w φ N).snd n +
      (weightedResonantCenterRemainder hp w φ N).snd n = _
    rw [weightedResonantLeadingTail_snd hp,hrem.2]
    by_cases hn : N ≤ n.natAbs <;>
      simp [weightedResonantCenterRemainderCoordinate,hn]
    ring

/-- The difference from the leading Fourier tail is the proved
actual remainder as a sequence pair. -/
theorem weightedResonantCenterClosingTail_sub_leading
    (hp : p ≠ ⊤) (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) :
    weightedResonantCenterClosingTail hp w φ N - weightedResonantLeadingTailCLM hp w N φ =
      weightedResonantCenterRemainder hp w φ N := by
  exact add_sub_cancel_left _ _

/-- The actual Banach analytic gap-closing map and its arbitrary joint
norm approximation by the signed Fourier tail share one neighborhood
for every larger cutoff. Its zero coordinates imply the original
periodic spectrum is a singleton of exact determinant order two. -/
theorem exists_uniform_analytic_weightedResonantCenterClosingTail
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ N : ℕ, N₀ ≤ N →
        AnalyticOnNhd ℂ (fun ψ => weightedResonantCenterClosingTail hp w ψ N) U ∧
        ∀ ψ ∈ U,
          ‖weightedResonantCenterClosingTail hp w ψ N-weightedResonantLeadingTailCLM hp w N ψ‖ < ε ∧
          ((∀ n : ℤ,
            (weightedResonantCenterClosingTail hp w ψ N).fst n =
              if N ≤ n.natAbs then (w (2*n) : ℂ)*weightedResonantBMinusExtension hp w ψ n
                (weightedResonantDiagonalCenter hp w ψ n) else 0) ∧
           (∀ n : ℤ,
            (weightedResonantCenterClosingTail hp w ψ N).snd n =
              if N ≤ n.natAbs then (w (2*n) : ℂ)*weightedResonantBPlusExtension hp w ψ n
                (weightedResonantDiagonalCenter hp w ψ n) else 0)) ∧
          ∀ n : ℤ, N ≤ n.natAbs →
            (weightedResonantCenterClosingTail hp w ψ N).fst n = 0 →
            (weightedResonantCenterClosingTail hp w ψ N).snd n = 0 →
            (∀ z ∈ resonantStrip n,
              z ∈ periodicSpectrum hp (weightedBaseToPair w ψ) ↔
                z = weightedResonantDiagonalCenter hp w ψ n) ∧
            ∀ z ∈ resonantStrip n,
              analyticOrderNatAt (resonantDeterminantExtension hp w ψ n) z =
                if z = weightedResonantDiagonalCenter hp w ψ n then 2 else 0 := by
  obtain ⟨N₁,hN₁,U₁,ho₁,hc₁,hφ₁,h0₁,h₁⟩ :=
    exists_uniform_analytic_weightedResonantCenterRemainder hp hp1 w φ ε hε
  obtain ⟨N₂,_,U₂,ho₂,hc₂,hφ₂,h0₂,h₂⟩ :=
    exists_uniform_weightedResonantDiagonalCenters hp hp1 w φ
  refine ⟨max N₁ N₂,hN₁.trans (le_max_left _ _),U₁ ∩ U₂,ho₁.inter ho₂,hc₁.inter hc₂,
    ⟨hφ₁,hφ₂⟩,⟨h0₁,h0₂⟩,?_⟩
  intro N hN
  have hrem := h₁ N (by omega)
  refine ⟨?_,?_⟩
  · intro ψ hψ
    exact ((weightedResonantLeadingTailCLM hp w N).analyticAt ψ).add (hrem.1 ψ hψ.1)
  · intro ψ hψ
    have hdata := hrem.2 ψ hψ.1
    have hcoord := weightedResonantCenterClosingTail_apply_of_mem hp w ψ N hdata.1
    refine ⟨?_,⟨fun n => (hcoord n).1,fun n => (hcoord n).2⟩,?_⟩
    · rw [weightedResonantCenterClosingTail_sub_leading]
      exact hdata.2
    · intro n hn hminus hplus
      have hw : (w (2*n) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (w.positive _).ne'
      have hminus0 : weightedResonantBMinusExtension hp w ψ n
          (weightedResonantDiagonalCenter hp w ψ n) = 0 := by
        rw [(hcoord n).1,if_pos hn] at hminus
        exact (mul_eq_zero.mp hminus).resolve_left hw
      have hplus0 : weightedResonantBPlusExtension hp w ψ n
          (weightedResonantDiagonalCenter hp w ψ n) = 0 := by
        rw [(hcoord n).2,if_pos hn] at hplus
        exact (mul_eq_zero.mp hplus).resolve_left hw
      exact (h₂ ψ hψ.2 n (by omega)).2.2.2 hplus0 hminus0

end NLS.ZakharovShabat
