import NLS.KdV.HillPeriodOnePotential
import NLS.SequenceSpaces.PositiveFourierTail
import NLS.SequenceSpaces.ReciprocalSquareTail

/-!
# Summed weighted Hill root gaps

The root separation theorem gives the source's high-frequency gap-tail
estimate after summation, with the corrected constant `2304` in the
quartic remainder. The root families are zeros of the actual constructed
determinant in their high strips; identifying them with global periodic
eigenvalue labels remains a separate spectral-enumeration obligation.
-/

noncomputable section
open scoped ENNReal
namespace NLS.KdV

/-- The individual weighted gap retains the source's constant six,
at the explicitly corrected cutoff `n>=8*norm(q)`. -/
theorem hillPeriodOne_gap_le (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) (n : ℕ) (hn : 1 ≤ n)
    (hcut : 8*‖q‖ ≤ (n : ℝ)) (z y : ℂ)
    (hz : z ∈ reducedHillStrip n) (hy : y ∈ reducedHillStrip n)
    (hdz : hillReducedDeterminant w n (hillPeriodOnePotential w q,z) = 0)
    (hdy : hillReducedDeterminant w n (hillPeriodOnePotential w q,y) = 0) :
    w (2*(n : ℤ))*‖z-y‖ ≤ 6*‖q‖ := by
  have hcoef := Coeff.pair_sq_le_norm_sq
    (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q)
    (n : ℤ) (-(n : ℤ)) (by omega)
  rw [hillPeriodOne_weighted_coefficient_sq, hillPeriodOne_weighted_coefficient_sq,
    mul_neg, w.apply_neg, ← WeightedCoeff.norm_eq] at hcoef
  have hroot := hillPeriodOne_roots_weighted_separation w q n hn hcut z y hz hy hdz hdy
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsq : 64*‖q‖^2 ≤ (n : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hcut) (show 0 ≤ (n : ℝ)+8*‖q‖ by positivity)]
  have hrem : 1152*‖q‖^4/(n : ℝ)^2 ≤ 18*‖q‖^2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hnpos)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsq (show 0 ≤ 18*‖q‖^2 by positivity)]
  have hnonneg : 0 ≤ w (2*(n : ℤ))*‖z-y‖ := mul_nonneg (w.positive _).le (norm_nonneg _)
  nlinarith [norm_nonneg q]

/-- A weighted high-frequency two-root family has a summable squared gap,
controlled by the actual source Fourier remainder and a quartic error. -/
theorem hillPeriodOne_gap_tail_bound (w : SpectralWeight)
    (q : WeightedCoeff w.doubleIndex.toWeight 2) (N : ℕ) (hN : 1 ≤ N)
    (hcut : 8*‖q‖ ≤ (N : ℝ)) (ξp ξm : ℕ → ℂ)
    (hp : ∀ n, N ≤ n → ξp n ∈ reducedHillStrip n)
    (hm : ∀ n, N ≤ n → ξm n ∈ reducedHillStrip n)
    (hdp : ∀ n, N ≤ n → hillReducedDeterminant w n (hillPeriodOnePotential w q,ξp n) = 0)
    (hdm : ∀ n, N ≤ n → hillReducedDeterminant w n (hillPeriodOnePotential w q,ξm n) = 0) :
    Summable (fun k : ℕ => (w (2*((k+N : ℕ) : ℤ)))^2*‖ξp (k+N)-ξm (k+N)‖^2) ∧
      (∑' k : ℕ, (w (2*((k+N : ℕ) : ℤ)))^2*‖ξp (k+N)-ξm (k+N)‖^2) ≤
        9*‖Coeff.fourierTail N (WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q)‖^2+
          2304*‖q‖^4/(N : ℝ) := by
  let a := WeightedCoeff.weightEquiv w.doubleIndex.toWeight 2 q
  let B := fun k : ℕ => ‖a ((k : ℤ)+N)‖^2+‖a (-((k : ℤ)+N))‖^2
  let R := fun k : ℕ => 1/((k : ℝ)+N)^2
  let C := 1152*‖q‖^4
  have hB : Summable B := (Coeff.positive_pair_tail_sq a N hN).1
  have hBn : (∑' k, B k) ≤ ‖Coeff.fourierTail N a‖^2 := (Coeff.positive_pair_tail_sq a N hN).2
  have hR : Summable R := ReciprocalSeries.summable_nat_reciprocal_sq_tail N hN
  have hRn : (∑' k, R k) ≤ 2/(N : ℝ) := ReciprocalSeries.tsum_nat_reciprocal_sq_tail_le N hN
  have hcoef (j : ℤ) : ‖a j‖^2 = (w (2*j))^2*‖q.val j‖^2 := by
    exact hillPeriodOne_weighted_coefficient_sq w q j
  have hmajor : Summable (fun k : ℕ => 9*B k+C*R k) :=
    (hB.mul_left 9).add (hR.mul_left C)
  have hpoint (k : ℕ) : (w (2*((k+N : ℕ) : ℤ)))^2*‖ξp (k+N)-ξm (k+N)‖^2 ≤ 9*B k+C*R k := by
    have hNk : N ≤ k+N := by omega
    have hkn : 1 ≤ k+N := hN.trans hNk
    have hcutk : 8*‖q‖ ≤ ((k+N : ℕ) : ℝ) := hcut.trans (by exact_mod_cast hNk)
    have h := hillPeriodOne_roots_weighted_separation w q (k+N) hkn hcutk
      (ξp (k+N)) (ξm (k+N)) (hp _ hNk) (hm _ hNk) (hdp _ hNk) (hdm _ hNk)
    apply h.trans_eq
    dsimp [B, C, R]
    rw [hcoef, hcoef, mul_neg, w.apply_neg]
    push_cast
    ring
  have hgap := Summable.of_nonneg_of_le (fun k : ℕ => by positivity) hpoint hmajor
  refine ⟨hgap, ?_⟩
  calc
    _ ≤ ∑' k : ℕ, (9*B k+C*R k) := hgap.tsum_le_tsum hpoint hmajor
    _ = 9*(∑' k, B k)+C*(∑' k, R k) := by
      rw [(hB.mul_left 9).tsum_add (hR.mul_left C), tsum_mul_left, tsum_mul_left]
    _ ≤ 9*‖Coeff.fourierTail N a‖^2+C*(2/(N : ℝ)) := by
      gcongr
    _ = _ := by dsimp [C, a]; ring

end NLS.KdV
