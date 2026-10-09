import NLS.ZakharovShabat.SourcePrintedHeightCounting
import NLS.ZakharovShabat.PrintedHeightFour

/-! # The unchanged source height and counting conclusions through p=4

The parameter uses the original period-one component-sum coefficient norm.
All counts, parity data, exclusions and actual analytic projections retain
their original definitions. Exponents above four remain unresolved.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original source spectrum lies within the printed strip for 1<=p<=4. -/
theorem sourceSpectrum_abs_im_lt_printed_height_up_to_four (hp : p ≠ ⊤) (hp4 : p ≤ 4)
    (φ : CoeffPair p) {z : ℂ} (hz : z ∈ periodicSpectrum hp (periodOnePotential φ)) :
    |z.im| < (1+8*‖φ‖)^p.toReal :=
  abs_im_lt_printed_height_up_to_four hp hp4 _ (norm_periodOnePotential_le φ) hz

/-- The printed boxes have the full central count and actual analytic projections
on one neighborhood, simultaneously with every larger frequency cutoff. -/
theorem exists_source_periodicCounting_printed_height_up_to_four (hp : p ≠ ⊤) (hp4 : p ≤ 4)
    (φ : CoeffPair p) :
    ∃ N₀ : ℕ, ∃ V : Set (CoeffPair p), 0 < N₀ ∧ IsOpen V ∧ Convex ℝ V ∧ φ ∈ V ∧ 0 ∈ V ∧
      ∀ N : ℕ, N₀ ≤ N →
        AnalyticOnNhd ℂ (fun ψ => heightRectangleIntegral hp (periodOnePotential ψ) N
          ((1+8*‖ψ‖)^p.toReal)) V ∧
        ∀ ψ ∈ V, PeriodicCountingData hp (periodOnePotential ψ) N ∧
          heightPeriodicSpectrum hp (periodOnePotential ψ) N ((1+8*‖ψ‖)^p.toReal) =
            centralPeriodicSpectrum hp (periodOnePotential ψ) N ∧
          (∑ z ∈ heightPeriodicSpectrum hp (periodOnePotential ψ) N ((1+8*‖ψ‖)^p.toReal),
            periodicAlgebraicMultiplicity hp (periodOnePotential ψ) z) = 4*N+2 ∧
          heightRectangleIntegral hp (periodOnePotential ψ) N ((1+8*‖ψ‖)^p.toReal) =
            centralSpectralProjection hp (periodOnePotential ψ) N ∧
          periodicSpectrum hp (periodOnePotential ψ) ⊆
            heightSpectralBox N ((1+8*‖ψ‖)^p.toReal) ∪ highSpectralDisks N (Real.pi/4) :=
  exists_source_periodicCounting_printed_height_of_resolvent hp
    (fun ψ _z hz => mem_resolventSet_of_printed_height_up_to_four hp hp4 _ (norm_periodOnePotential_le ψ) hz) φ

end NLS.ZakharovShabat
