import NLS.KdV.HillEventualActionGapBound
import NLS.KdV.HillCanonicalGapBounds
import NLS.KdV.HillL2HighGapMoments

/-! # Weighted summability of actual real-gap Hill actions

The action is the real-gap integral of the actual period-one Hill trace.
It agrees with the source-normalized Arnold contour at every checked
high index. Eventual quadratic action-gap control and the corrected
weighted gap tail theorem prove weighted action summability. The cutoff
in the action comparison is potential dependent, so the explicit uniform
inequalities of Theorem 3 and the Birkhoff-map identification remain open.
-/

noncomputable section
open Set Complex
namespace NLS.KdV

def hillPeriodOneAction (w : SpectralWeight) (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hr : IsRealHillPotential (w.doubleIndex.toCoeff q)) (n : ℕ) : ℝ :=
  hillRealGapIntegral (hillPeriodOneUnitPotential w q) (hillPeriodOneUnitPotential_even w q)
    (hillPeriodOneUnitPotential_real w q hr) n 0

theorem hillRealGapIntegral_congr
    (q p : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hp : SpectralWeight.one.toCoeff p ∈ Coeff.paritySubspace 0)
    (hrq : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (hrp : IsRealHillPotential (SpectralWeight.one.toCoeff p))
    (he : q = p) (n m : ℕ) :
    hillRealGapIntegral q hq hrq n m = hillRealGapIntegral p hp hrp n m := by
  subst p
  rfl

/-- The action depends on the physical Fourier coefficients, independently
of the auxiliary spectral weight used to present the same potential. -/
theorem hillPeriodOneAction_eq_of_coeff_eq (w v : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) (p : WeightedCoeff v.doubleIndex.toWeight 2)
    (hrq : IsRealHillPotential (w.doubleIndex.toCoeff q))
    (hrp : IsRealHillPotential (v.doubleIndex.toCoeff p))
    (he : ∀ k : ℤ, q.val k = p.val k) (n : ℕ) :
    hillPeriodOneAction w q hrq n = hillPeriodOneAction v p hrp n :=
  hillRealGapIntegral_congr _ _ _ _ _ _ (hillPeriodOneUnitPotential_eq_of_coeff_eq w v q p he) n 0

theorem hillPeriodOneAction_nonneg (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hr : IsRealHillPotential (w.doubleIndex.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ hillPeriodOneAction w q hr n := by
  simpa only [hillPeriodOneAction, mul_zero] using hillRealGapIntegral_nonneg_even
    (hillPeriodOneUnitPotential w q) (hillPeriodOneUnitPotential_even w q)
    (hillPeriodOneUnitPotential_real w q hr) n hn 0

theorem hillPeriodOneAction_eq_highContourMoment (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hr : IsRealHillPotential (w.doubleIndex.toCoeff q)) (n : ℕ) (hn : 2 ≤ n)
    (hcut : 8 * ‖q‖ ≤ (n : ℝ)) :
    hillL2HighContourMoment n 0 (w.toCoeff (hillPeriodOnePotential w q)) =
      (hillPeriodOneAction w q hr n : ℂ) := by
  rw [← toCoeff_hillPeriodOneUnitPotential]
  exact hillL2HighContourMoment_eq_gapIntegral (hillPeriodOneUnitPotential w q)
    (hillPeriodOneUnitPotential_even w q) (hillPeriodOneUnitPotential_real w q hr) n hn
    (by linarith [norm_hillPeriodOneUnitPotential_le w q]) 0

/-- A potential-dependent cutoff suffices for the quantitative tail
comparison with the corrected Appendix A.7 gap remainder. -/
theorem exists_hillPeriodOneAction_weighted_tail_bound (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hr : IsRealHillPotential (w.doubleIndex.toCoeff q)) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → 8 * ‖q‖ ≤ (N : ℝ) →
      Summable (fun k : ℕ => w (2 * ((k + N : ℕ) : ℤ)) ^ 2 *
        (2 * Real.pi * (k + N : ℕ)) * hillPeriodOneAction w q hr (k + N)) ∧
      (∑' k : ℕ, w (2 * ((k + N : ℕ) : ℤ)) ^ 2 *
        (2 * Real.pi * (k + N : ℕ)) * hillPeriodOneAction w q hr (k + N)) ≤
        (2 * Real.pi) *
          (9 * ‖Coeff.fourierTail N (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q)‖ ^ 2 +
            2304 * ‖q‖ ^ 4 / (N : ℝ)) := by
  obtain ⟨N₀, hN₀, haction⟩ := exists_hillRealGapIntegral_quadratic_tail_bound
    (hillPeriodOneUnitPotential w q) (hillPeriodOneUnitPotential_even w q)
    (hillPeriodOneUnitPotential_real w q hr)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN hcut
  obtain ⟨hgap, hgapbound⟩ := hillPeriodOne_canonical_gap_tail_bound w q hr N (hN₀.trans hN) hcut
  have hpoint (k : ℕ) : w (2 * ((k + N : ℕ) : ℤ)) ^ 2 *
      (2 * Real.pi * (k + N : ℕ)) * hillPeriodOneAction w q hr (k + N) ≤
        (2 * Real.pi) * (w (2 * ((k + N : ℕ) : ℤ)) ^ 2 * hillPeriodOneGap w q hr (k + N) ^ 2) := by
    have hb := haction (k + N) (by omega)
    change ((k + N : ℕ) : ℝ) * hillPeriodOneAction w q hr (k + N) ≤
      hillPeriodOneGap w q hr (k + N) ^ 2 at hb
    calc
      _ = (2 * Real.pi) * (w (2 * ((k + N : ℕ) : ℤ)) ^ 2 *
          (((k + N : ℕ) : ℝ) * hillPeriodOneAction w q hr (k + N))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hb (sq_nonneg _)) (by positivity)
  have hs := Summable.of_nonneg_of_le (fun k =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity))
      (hillPeriodOneAction_nonneg w q hr (k + N) (by omega))) hpoint
    (hgap.mul_left (2 * Real.pi))
  refine ⟨hs, ?_⟩
  have hsum := hs.tsum_le_tsum hpoint (hgap.mul_left (2 * Real.pi))
  rw [tsum_mul_left] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_left hgapbound (by positivity))

/-- The source action sequence has finite weighted l1 norm, with the
exact source `w(2*n)^2*(2*pi*n)` factor and positive-index convention. -/
theorem summable_hillPeriodOneAction_weighted (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2)
    (hr : IsRealHillPotential (w.doubleIndex.toCoeff q)) :
    Summable (fun k : ℕ => w (2 * ((k + 1 : ℕ) : ℤ)) ^ 2 *
      (2 * Real.pi * (k + 1 : ℕ)) * hillPeriodOneAction w q hr (k + 1)) := by
  obtain ⟨N₀, _, htail⟩ := exists_hillPeriodOneAction_weighted_tail_bound w q hr
  obtain ⟨A, hA⟩ := exists_nat_ge (8 * ‖q‖)
  let N := max N₀ A
  have hs := (htail N (le_max_left _ _) (hA.trans (by exact_mod_cast le_max_right N₀ A))).1
  have hfull : Summable (fun k : ℕ => w (2 * (k : ℤ)) ^ 2 *
      (2 * Real.pi * (k : ℝ)) * hillPeriodOneAction w q hr k) :=
    (summable_nat_add_iff N).mp hs
  simpa only [Function.comp_def, Nat.succ_eq_add_one] using hfull.comp_injective Nat.succ_injective

end NLS.KdV
