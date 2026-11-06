import NLS.KdV.HillRealActionContinuity
import NLS.KdV.HillWeightedRealActions
import NLS.KdV.HillActionTailBudget
import NLS.SequenceSpaces.LocalSeriesContinuity

/-! # Locally uniform weighted tails of actual Hill actions

The intrinsic real L2 neighborhood bound pulls back to native period-one
weighted coefficients. The corrected Fourier gap-tail budget then bounds
the summed actual action tail with one cutoff on a neighborhood.
-/

noncomputable section
open Set Complex Filter Topology
namespace NLS.KdV

theorem continuous_hillPeriodOneUnitPotential (w : SpectralWeight) :
    Continuous (hillPeriodOneUnitPotential w) := by
  unfold hillPeriodOneUnitPotential
  exact
    (hillForgetWeight w 2).continuous.comp (hillPeriodOnePotential w).continuous

abbrev RealHillWeightedPotential (w : SpectralWeight) :=
  {p : WeightedCoeff w.doubleIndex.toWeight 2 // IsRealHillPotential (w.doubleIndex.toCoeff p)}

def hillRealWeightedEmbedding (w : SpectralWeight) :
    RealHillWeightedPotential w → RealPeriodOneHillPotential := fun p =>
  ⟨hillPeriodOneUnitPotential w p.val, hillPeriodOneUnitPotential_even w p.val,
    hillPeriodOneUnitPotential_real w p.val p.property⟩

theorem continuous_hillRealWeightedEmbedding (w : SpectralWeight) :
    Continuous (hillRealWeightedEmbedding w) :=
  ((continuous_hillPeriodOneUnitPotential w).comp continuous_subtype_val).subtype_mk _

theorem hillPeriodOneAction_quadratic_predicate_embedding
    (w : SpectralWeight) (p : RealHillWeightedPotential w) (n : ℕ) :
    ((n : ℝ) * hillPeriodOneAction w p.val p.property n ≤
      hillPeriodOneGap w p.val p.property n ^ 2) =
    ((n : ℝ) * hillRealGapIntegral (hillRealWeightedEmbedding w p).val
      (hillRealWeightedEmbedding w p).property.1
      (hillRealWeightedEmbedding w p).property.2 n 0 ≤
      (hillRealLabels (hillRealWeightedEmbedding w p).val
        (hillRealWeightedEmbedding w p).property.1
        (hillRealWeightedEmbedding w p).property.2 (2*n) -
      hillRealLabels (hillRealWeightedEmbedding w p).val
        (hillRealWeightedEmbedding w p).property.1
        (hillRealWeightedEmbedding w p).property.2 (2*n-1))^2) := rfl

theorem exists_hillPeriodOneAction_local_quadratic_bound
    (w : SpectralWeight) (q : RealHillWeightedPotential w) :
    ∃ N₀ : ℕ, ∃ U : Set (RealHillWeightedPotential w),
      2 ≤ N₀ ∧ IsOpen U ∧ q ∈ U ∧ ∀ p ∈ U, ∀ n : ℕ, N₀ ≤ n →
        (n : ℝ) * hillPeriodOneAction w p.val p.property n ≤
          hillPeriodOneGap w p.val p.property n ^ 2 := by
  exact exists_local_nat_property_pullback 2 (hillRealWeightedEmbedding w)
    (continuous_hillRealWeightedEmbedding w)
    (fun p n => (n : ℝ) * hillRealGapIntegral p.val p.property.1 p.property.2 n 0 ≤
      (hillRealLabels p.val p.property.1 p.property.2 (2*n) -
        hillRealLabels p.val p.property.1 p.property.2 (2*n-1))^2)
    (fun p n => (n : ℝ) * hillPeriodOneAction w p.val p.property n ≤
      hillPeriodOneGap w p.val p.property n ^ 2)
    (hillPeriodOneAction_quadratic_predicate_embedding w) q
    (exists_hillRealGapIntegral_uniform_local_tail (hillRealWeightedEmbedding w q))

theorem exists_hillPeriodOneAction_local_weighted_tail_bound
    (w : SpectralWeight) (q : RealHillWeightedPotential w) :
    ∃ N₀ : ℕ, ∃ U : Set (RealHillWeightedPotential w),
      2 ≤ N₀ ∧ IsOpen U ∧ q ∈ U ∧ ∀ p ∈ U,
      ∀ N : ℕ, N₀ ≤ N → 8 * ‖p.val‖ ≤ (N : ℝ) →
      Summable (fun k : ℕ => w (2 * ((k + N : ℕ) : ℤ)) ^ 2 *
        (2 * Real.pi * (k + N : ℕ)) * hillPeriodOneAction w p.val p.property (k + N)) ∧
      (∑' k : ℕ, w (2 * ((k + N : ℕ) : ℤ)) ^ 2 *
        (2 * Real.pi * (k + N : ℕ)) * hillPeriodOneAction w p.val p.property (k + N)) ≤
        (2 * Real.pi) *
          (9 * ‖Coeff.fourierTail N (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 p.val)‖ ^ 2 +
            2304 * ‖p.val‖ ^ 4 / (N : ℝ)) := by
  obtain ⟨N₀, U, hN₀, hU, hqU, hbound⟩ :=
    exists_hillPeriodOneAction_local_quadratic_bound w q
  refine ⟨N₀, U, hN₀, hU, hqU, ?_⟩
  intro p hp N hN hcut
  apply hillPeriodOneAction_weighted_tail_of_quadratic_bound w p.val p.property N
    (hN₀.trans hN) hcut
  intro n hn
  exact hbound p hp n (hN.trans hn)


end NLS.KdV
