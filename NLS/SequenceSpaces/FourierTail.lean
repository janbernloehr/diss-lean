import NLS.SequenceSpaces.Truncation
import NLS.SequenceSpaces.DominatedConvergence
import Mathlib.Data.Int.Interval

/-!
# Symmetric Fourier tails and separated frequency windows

The tail retains `|k| ≥ N`, including the boundary, as in the dissertation's
remainder `R_n` with `N = |n|`. Near windows about the opposite scalar Fourier
frequencies `-n` and `n` only couple through this tail.
-/

open scoped ENNReal
open Filter
noncomputable section

namespace NLS.Coeff

/-- Frequencies strictly inside the cutoff radius. -/
def lowFrequencies (N : ℕ) : Finset ℤ := Finset.Ioo (-(N : ℤ)) N

@[simp] theorem mem_lowFrequencies (N : ℕ) (j : ℤ) :
    j ∈ lowFrequencies N ↔ j.natAbs < N := by
  simp only [lowFrequencies, Finset.mem_Ioo]
  omega

/-- A closed frequency window about an integer center. -/
def frequencyWindow (c : ℤ) (N : ℕ) : Finset ℤ := Finset.Icc (c - N) (c + N)

@[simp] theorem mem_frequencyWindow (c : ℤ) (N : ℕ) (j : ℤ) :
    j ∈ frequencyWindow c N ↔ (j - c).natAbs ≤ N := by
  simp only [frequencyWindow, Finset.mem_Icc]
  omega

/-- The potential frequencies coupling the two near windows belong to `R_n`. -/
theorem opposite_frequencyWindows_separated (n : ℤ) :
    ∀ j ∈ frequencyWindow (-n) (n.natAbs / 2),
      ∀ k ∈ frequencyWindow n (n.natAbs / 2), j - k ∉ lowFrequencies n.natAbs := by
  intro j hj k hk
  simp only [mem_frequencyWindow, mem_lowFrequencies] at *
  omega

variable {p : ℝ≥0∞}

/-- The symmetric Fourier remainder, retaining the boundary `|j| = N`. -/
def fourierTail (N : ℕ) (a : Coeff p) : Coeff p := a - truncate (lowFrequencies N) a

@[simp] theorem fourierTail_apply (N : ℕ) (a : Coeff p) (j : ℤ) :
    fourierTail N a j = if N ≤ j.natAbs then a j else 0 := by
  change a j - truncate (lowFrequencies N) a j = _
  by_cases hj : j.natAbs < N <;> simp [hj, Nat.not_le_of_lt, Nat.le_of_not_gt]

@[simp] theorem fourierTail_zero (a : Coeff p) : fourierTail 0 a = a := by
  ext j
  simp

@[simp] theorem fourierTail_fourierTail (M N : ℕ) (a : Coeff p) :
    fourierTail M (fourierTail N a) = fourierTail (max M N) a := by
  ext j
  by_cases hM : M ≤ j.natAbs <;> by_cases hN : N ≤ j.natAbs <;> simp [hM, hN]

/-- A single Fourier mode survives exactly when it lies on or beyond the cutoff. -/
@[simp] theorem fourierTail_single (N : ℕ) (k : ℤ) (c : ℂ) :
    fourierTail N (lp.single p k c) = if N ≤ k.natAbs then lp.single p k c else 0 := by
  ext j
  by_cases hj : j = k
  · subst j
    by_cases hN : N ≤ k.natAbs <;> simp [hN]
  · by_cases hN : N ≤ k.natAbs <;> simp [hN, lp.single_apply, hj]

theorem norm_fourierTail_le (hp : p ≠ 0) (N : ℕ) (a : Coeff p) :
    ‖fourierTail N a‖ ≤ ‖a‖ := norm_sub_truncate_le hp _ _

theorem norm_fourierTail_antitone (hp : p ≠ 0) (a : Coeff p) :
    Antitone (fun N => ‖fourierTail N a‖) := by
  intro M N hMN
  simpa only [fourierTail_fourierTail, max_eq_left hMN] using
    norm_fourierTail_le hp N (fourierTail M a)

/-- The remainder tends to zero in norm at every finite Banach exponent. -/
theorem tendsto_fourierTail [Fact (1 ≤ p)] (hp : p ≠ ⊤) (a : Coeff p) :
    Tendsto (fun N : ℕ => fourierTail N a) atTop (nhds 0) := by
  apply tendsto_zero_of_dominated hp _ a
  · exact Eventually.of_forall fun N j => by
      rw [fourierTail_apply]
      split <;> simp
  · intro j
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (j.natAbs + 1)] with N hN
    rw [fourierTail_apply, if_neg (by omega)]

end NLS.Coeff
