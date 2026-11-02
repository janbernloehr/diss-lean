import NLS.SequenceSpaces.Multiplier
import NLS.SequenceSpaces.Weighted
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# The reduced free Hill resolvent

The period-two Fourier basis is `exp (i * pi * k * x)`, so `-d²/dx²`
has symbol `pi² * k²`. This file constructs the inverse of `lambda + d²/dx²`
away from the modes `±n`. It does not identify the spectrum of a perturbed
Hill operator or assert the existence of KdV Birkhoff coordinates.

The strip radius is `6*n`. Every result below includes this explicit choice;
no wider strip convention from another source is silently imported.
-/

noncomputable section
open scoped ENNReal

namespace NLS.KdV

/-- The free Hill eigenvalue attached to a signed period-two Fourier mode. -/
def freeHillValue (k : ℤ) : ℝ := Real.pi ^ 2 * (k : ℝ) ^ 2

@[simp] theorem freeHillValue_neg (k : ℤ) : freeHillValue (-k) = freeHillValue k := by
  simp [freeHillValue]

/-- A strip on which all modes except `±n` are uniformly separated. -/
def reducedHillStrip (n : ℕ) : Set ℂ :=
  {z | |z.re - freeHillValue n| ≤ 6 * (n : ℝ)}

/-- Distinct squared integer modes have a gap at least the positive mode index. -/
theorem nat_le_abs_sq_sub_sq {n : ℕ} (hn : 1 ≤ n) {k : ℤ}
    (hk : k.natAbs ≠ n) :
    (n : ℝ) ≤ |(n : ℝ) ^ 2 - (k : ℝ) ^ 2| := by
  have h : (n : ℤ) ≤ |(n : ℤ) ^ 2 - k ^ 2| := by
    have hkn : |k| ≠ (n : ℤ) := by
      intro he
      apply hk
      have he' : (k.natAbs : ℤ) = (n : ℤ) := by simpa using he
      exact_mod_cast he'
    have hn' : (1 : ℤ) ≤ n := by exact_mod_cast hn
    rcases lt_or_gt_of_ne hkn with hlt | hgt
    · have hle : |k| ≤ (n : ℤ) - 1 := by omega
      have hnonneg : (0 : ℤ) ≤ |k| := abs_nonneg k
      have hsq : k ^ 2 ≤ ((n : ℤ) - 1) ^ 2 := by nlinarith [sq_abs k]
      rw [abs_of_nonneg (show 0 ≤ (n : ℤ)^2-k^2 by nlinarith)]
      nlinarith
    · have hle : (n : ℤ) + 1 ≤ |k| := by omega
      have hsq : ((n : ℤ) + 1)^2 ≤ k^2 := by nlinarith [sq_abs k]
      rw [abs_of_nonpos (show (n : ℤ)^2-k^2 ≤ 0 by nlinarith)]
      nlinarith
  exact_mod_cast h

/-- The quadratic Hill lattice remains separated on the chosen strip. -/
theorem freeHill_denominator_lower {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : z ∈ reducedHillStrip n) {k : ℤ} (hk : k.natAbs ≠ n) :
    |(n : ℝ)^2 - (k : ℝ)^2| ≤ ‖z - (freeHillValue k : ℂ)‖ := by
  let d : ℝ := |(n : ℝ)^2 - (k : ℝ)^2|
  have hnd : (n : ℝ) ≤ d := nat_le_abs_sq_sub_sq hn hk
  have hpi : 9 < Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have he : Real.pi ^ 2 * d = |freeHillValue n - freeHillValue k| := by
    dsimp [d, freeHillValue]
    simp only [Int.cast_natCast]
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg Real.pi)]
  have ht : Real.pi ^ 2 * d ≤ 6 * (n : ℝ) + ‖z - (freeHillValue k : ℂ)‖ := by
    rw [he]
    calc
      |freeHillValue n - freeHillValue k| ≤
          |freeHillValue n - z.re| + |z.re - freeHillValue k| := by
        simpa using abs_add_le (freeHillValue n - z.re) (z.re - freeHillValue k)
      _ ≤ 6 * (n : ℝ) + ‖z - (freeHillValue k : ℂ)‖ := by
        apply add_le_add
        · simpa only [reducedHillStrip, Set.mem_ofPred_eq, abs_sub_comm] using hz
        · simpa using Complex.abs_re_le_norm (z - (freeHillValue k : ℂ))
  have hd : 0 ≤ d := abs_nonneg _
  nlinarith

/-- In particular every retained denominator is at least `n`. -/
theorem freeHill_denominator_ge_index {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : z ∈ reducedHillStrip n) {k : ℤ} (hk : k.natAbs ≠ n) :
    (n : ℝ) ≤ ‖z - (freeHillValue k : ℂ)‖ :=
  (nat_le_abs_sq_sub_sq hn hk).trans (freeHill_denominator_lower hn hz hk)

theorem freeHill_denominator_ne_zero {n : ℕ} (hn : 1 ≤ n) {z : ℂ}
    (hz : z ∈ reducedHillStrip n) {k : ℤ} (hk : k.natAbs ≠ n) :
    z - (freeHillValue k : ℂ) ≠ 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  exact norm_pos_iff.mp (hn'.trans_le (freeHill_denominator_ge_index hn hz hk))

/-- Bounded reciprocal symbol with the resonant modes removed. -/
def reducedHillSymbol (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hz : z ∈ reducedHillStrip n) : Coeff ⊤ :=
  ⟨fun k => if k.natAbs = n then 0 else (z - (freeHillValue k : ℂ))⁻¹,
    memℓp_infty ⟨(n : ℝ)⁻¹, by
      rintro _ ⟨k, rfl⟩
      by_cases hk : k.natAbs = n
      · simp only [if_pos hk, norm_zero]; positivity
      · simp only [if_neg hk, norm_inv]
        exact inv_anti₀ (by exact_mod_cast (show 0 < n by omega))
          (freeHill_denominator_ge_index hn hz hk)⟩⟩

/-- The reduced inverse, on every Banach coefficient space including `p = ∞`. -/
def reducedHillResolvent {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    Coeff p →L[ℂ] Coeff p :=
  Coeff.multiplierCLM (reducedHillSymbol n hn z hz)

@[simp] theorem reducedHillResolvent_apply {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (a : Coeff p) (k : ℤ) :
    reducedHillResolvent n hn z hz a k =
      if k.natAbs = n then 0 else (z - (freeHillValue k : ℂ))⁻¹ * a k := by
  change (if k.natAbs = n then 0 else _) * a k = _
  split_ifs <;> simp

/-- Multiplying back by the Hill symbol gives the projection deleting `±n`. -/
theorem reducedHillResolvent_right_inverse {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (a : Coeff p) (k : ℤ) :
    (z - (freeHillValue k : ℂ)) * reducedHillResolvent n hn z hz a k =
      if k.natAbs = n then 0 else a k := by
  rw [reducedHillResolvent_apply]
  split_ifs with hk
  · simp
  · rw [← mul_assoc, mul_inv_cancel₀ (freeHill_denominator_ne_zero hn hz hk), one_mul]

/-- Uniform bound obtained from the generic sequence multiplier theorem. -/
theorem norm_reducedHillResolvent_apply_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n) (a : Coeff p) :
    ‖reducedHillResolvent n hn z hz a‖ ≤ (n : ℝ)⁻¹ * ‖a‖ := by
  apply (Coeff.norm_multiplier_le (reducedHillSymbol n hn z hz) a).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg a)
  apply lp.norm_le_of_forall_le (by positivity)
  intro k
  change ‖if k.natAbs = n then (0 : ℂ) else _‖ ≤ _
  split_ifs with hk
  · simp
  · rw [norm_inv]
    exact inv_anti₀ (by exact_mod_cast (show 0 < n by omega))
      (freeHill_denominator_ge_index hn hz hk)

/-- The same diagonal inverse acts on every positive weighted Banach space.
No symmetry, submultiplicativity or growth condition on the weight is needed. -/
def weightedReducedHillResolvent {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (w : Weight) (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n) :
    WeightedCoeff w p →L[ℂ] WeightedCoeff w p :=
  WeightedCoeff.weightIsometry w p |>.toContinuousLinearEquiv |>.symm.toContinuousLinearMap |>.comp
    ((reducedHillResolvent n hn z hz).comp
      (WeightedCoeff.weightIsometry w p).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem weightedReducedHillResolvent_apply {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (w : Weight) (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (a : WeightedCoeff w p) (k : ℤ) :
    (weightedReducedHillResolvent w n hn z hz a).val k =
      if k.natAbs = n then 0 else (z - (freeHillValue k : ℂ))⁻¹ * a.val k := by
  change reducedHillResolvent n hn z hz (WeightedCoeff.weightEquiv w p a) k /
    (w k : ℂ) = _
  rw [reducedHillResolvent_apply, WeightedCoeff.weightEquiv_apply]
  split_ifs with hk
  · simp
  · field_simp [w.complex_ne_zero k]

theorem norm_weightedReducedHillResolvent_apply_le {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (w : Weight) (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (a : WeightedCoeff w p) :
    ‖weightedReducedHillResolvent w n hn z hz a‖ ≤ (n : ℝ)⁻¹ * ‖a‖ := by
  change ‖(WeightedCoeff.weightIsometry w p).symm
    (reducedHillResolvent n hn z hz (WeightedCoeff.weightIsometry w p a))‖ ≤ _
  rw [(WeightedCoeff.weightIsometry w p).symm.norm_map]
  exact (norm_reducedHillResolvent_apply_le n hn z hz _).trans_eq
    (by rw [(WeightedCoeff.weightIsometry w p).norm_map])

/-- Uniqueness in the complement of the two resonant modes. -/
theorem reducedHillResolvent_unique {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (n : ℕ) (hn : 1 ≤ n) (z : ℂ) (hz : z ∈ reducedHillStrip n)
    (a b : Coeff p) (hzero : ∀ k, k.natAbs = n → b k = 0)
    (heq : ∀ k, k.natAbs ≠ n → (z - (freeHillValue k : ℂ)) * b k = a k) :
    b = reducedHillResolvent n hn z hz a := by
  ext k
  rw [reducedHillResolvent_apply]
  split_ifs with hk
  · exact hzero k hk
  · rw [← heq k hk, ← mul_assoc,
      inv_mul_cancel₀ (freeHill_denominator_ne_zero hn hz hk), one_mul]

end NLS.KdV
