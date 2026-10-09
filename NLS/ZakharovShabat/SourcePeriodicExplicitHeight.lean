import NLS.ZakharovShabat.SourcePrintedHeightCounting

/-! # A proposed all-exponent correction to the periodic counting height

The sufficient source height (1+8pM)^p retains the original Fourier pair
norm. It gives actual resolvent edges, counting, exhaustion, parity, and
analytic moving rectangular projections on a common source neighborhood.
This is a separate corrected statement, not the refuted printed height.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The proposed source-norm height, with its exponent dependence retained. -/
def sourcePeriodicExplicitHeight (p : ℝ≥0∞) (M : ℝ) : ℝ :=
  (1+8*p.toReal*M)^p.toReal

omit [Fact (1 ≤ p)] in
theorem sourcePeriodicExplicitHeight_pos {M : ℝ} (hM : 0 ≤ M) :
    0 < sourcePeriodicExplicitHeight p M := by
  unfold sourcePeriodicExplicitHeight
  positivity

omit [Fact (1 ≤ p)] in
theorem sourcePeriodicExplicitHeight_mono {M R : ℝ} (hM : 0 ≤ M) (hMR : M ≤ R) :
    sourcePeriodicExplicitHeight p M ≤ sourcePeriodicExplicitHeight p R := by
  unfold sourcePeriodicExplicitHeight
  gcongr

/-- Both edges and the closed exterior strip belong to the actual source resolvent. -/
theorem mem_resolventSet_of_sourcePeriodicExplicitHeight (hp : p ≠ ⊤)
    (φ : CoeffPair p) {M : ℝ} (hφ : ‖φ‖ ≤ M) {z : ℂ}
    (hz : sourcePeriodicExplicitHeight p M ≤ |z.im|) :
    z ∈ resolventSet hp (periodOnePotential φ) :=
  mem_resolventSet_of_explicit_height hp _ ((norm_periodOnePotential_le φ).trans hφ) hz

/-- All actual source spectral points lie strictly below the proposed norm-ball height. -/
theorem sourcePeriodicSpectrum_abs_im_lt_explicit_height (hp : p ≠ ⊤)
    (φ : CoeffPair p) {M : ℝ} (hφ : ‖φ‖ ≤ M) {z : ℂ}
    (hz : z ∈ periodicSpectrum hp (periodOnePotential φ)) :
    |z.im| < sourcePeriodicExplicitHeight p M :=
  abs_im_lt_explicit_height hp _ ((norm_periodOnePotential_le φ).trans hφ) hz

/-- The proposed height retains the full source counting data on one common neighborhood,
for every larger cutoff, including the actual analytic rectangular projection. -/
theorem sourceTheorem1_1_proposed_height (hp : p ≠ ⊤) (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ V : Set (CoeffPair p), 0 < N₀ ∧ IsOpen V ∧ Convex ℝ V ∧ φ ∈ V ∧ 0 ∈ V ∧
      ∀ N : ℕ, N₀ ≤ N →
        AnalyticOnNhd ℂ (fun ψ => heightRectangleIntegral hp (periodOnePotential ψ) N
          (sourcePeriodicExplicitHeight p ‖ψ‖)) V ∧
        ∀ ψ ∈ V, PeriodicCountingData hp (periodOnePotential ψ) N ∧
          heightPeriodicSpectrum hp (periodOnePotential ψ) N (sourcePeriodicExplicitHeight p ‖ψ‖) =
            centralPeriodicSpectrum hp (periodOnePotential ψ) N ∧
          (∑ z ∈ heightPeriodicSpectrum hp (periodOnePotential ψ) N (sourcePeriodicExplicitHeight p ‖ψ‖),
            periodicAlgebraicMultiplicity hp (periodOnePotential ψ) z) = 4*N+2 ∧
          heightRectangleIntegral hp (periodOnePotential ψ) N (sourcePeriodicExplicitHeight p ‖ψ‖) =
            centralSpectralProjection hp (periodOnePotential ψ) N ∧
          periodicSpectrum hp (periodOnePotential ψ) ⊆
            heightSpectralBox N (sourcePeriodicExplicitHeight p ‖ψ‖) ∪ highSpectralDisks N (Real.pi/4) :=
  exists_source_periodicCounting_coefficient_height_of_resolvent hp (8*p.toReal) (by positivity)
    (fun ψ _z hz => mem_resolventSet_of_sourcePeriodicExplicitHeight hp ψ le_rfl hz) φ

end NLS.ZakharovShabat
