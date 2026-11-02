import NLS.ZakharovShabat.PeriodTwoPrintedHeightCounting
import NLS.ZakharovShabat.SourcePeriodicExplicitHeight
import NLS.ZakharovShabat.RealType

/-! # Corrected Proposition 3.1 on the full period-two source space

The height `(1 + 8 * p * ‖φ‖)^p` retains the original source norm for
every finite Banach exponent, including one. No period-one support
assumption is imposed. The counting data keeps the conditional parity
clauses, full algebraic multiplicities and actual contour projections.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The corrected height puts both edges and the full exterior strip in
the actual period-two resolvent, using the original norm ball. -/
theorem mem_resolventSet_of_periodTwoExplicitHeight (hp : p ≠ ⊤)
    (φ : CoeffPair p) {M : ℝ} (hφ : ‖φ‖ ≤ M) {z : ℂ}
    (hz : sourcePeriodicExplicitHeight p M ≤ |z.im|) :
    z ∈ resolventSet hp (CoeffPair.toMax p φ) :=
  mem_resolventSet_of_explicit_height hp _ ((CoeffPair.norm_toMax_le φ).trans hφ) hz

/-- The corrected Proposition 3.1 package on the entire original period-two
space: common source neighborhood, all larger cutoffs, discrete spectrum,
reality, exact counts and parity, and analytic moving-height projections. -/
theorem exists_periodTwo_periodicCounting_corrected_height (hp : p ≠ ⊤)
    (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ V : Set (CoeffPair p),
      0 < N₀ ∧ IsOpen V ∧ Convex ℝ V ∧ φ ∈ V ∧ 0 ∈ V ∧
      ∀ N : ℕ, N₀ ≤ N →
        AnalyticOnNhd ℂ (fun ψ => heightRectangleIntegral hp (CoeffPair.toMax p ψ) N
          (sourcePeriodicExplicitHeight p ‖ψ‖)) V ∧
        ∀ ψ ∈ V,
          DiscreteTopology (periodicSpectrum hp (CoeffPair.toMax p ψ)) ∧
          (IsRealType (CoeffPair.toMax p ψ) →
            ∀ z ∈ periodicSpectrum hp (CoeffPair.toMax p ψ), z.im = 0) ∧
          PeriodicCountingData hp (CoeffPair.toMax p ψ) N ∧
          heightPeriodicSpectrum hp (CoeffPair.toMax p ψ) N (sourcePeriodicExplicitHeight p ‖ψ‖) =
            centralPeriodicSpectrum hp (CoeffPair.toMax p ψ) N ∧
          (∑ z ∈ heightPeriodicSpectrum hp (CoeffPair.toMax p ψ) N
            (sourcePeriodicExplicitHeight p ‖ψ‖),
            periodicAlgebraicMultiplicity hp (CoeffPair.toMax p ψ) z) = 4 * N + 2 ∧
          heightRectangleIntegral hp (CoeffPair.toMax p ψ) N (sourcePeriodicExplicitHeight p ‖ψ‖) =
            centralSpectralProjection hp (CoeffPair.toMax p ψ) N ∧
          periodicSpectrum hp (CoeffPair.toMax p ψ) ⊆
            heightSpectralBox N (sourcePeriodicExplicitHeight p ‖ψ‖) ∪
              highSpectralDisks N (Real.pi / 4) := by
  obtain ⟨N₀, V, hN₀, ho, hc, hφ, h0, hall⟩ :=
    exists_periodTwo_periodicCounting_coefficient_height_of_resolvent hp (8 * p.toReal)
      (by positivity) (fun ψ _z hz => mem_resolventSet_of_periodTwoExplicitHeight hp ψ le_rfl hz) φ
  refine ⟨N₀, V, hN₀, ho, hc, hφ, h0, ?_⟩
  intro N hN
  obtain ⟨han, hd⟩ := hall N hN
  refine ⟨han, ?_⟩
  intro ψ hψ
  exact ⟨discreteTopology_periodicSpectrum hp _,
    fun hreal z hz => periodicSpectrum_im_eq_zero_of_realType hp _ hreal z hz, hd ψ hψ⟩

end NLS.ZakharovShabat
