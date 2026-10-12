import NLS.ZakharovShabat.SourceFreeResolvent

/-! # Lemma 3.2(ii) fails in the original pair norms

The two constant components at p=2 and z=i/10000 give a finite Fourier
counterexample to the printed operator bound. No asymptotic or spectral
counterexample construction is needed.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

def lemma3_2CounterexampleInput : CoeffPair 2 := WithLp.toLp 2 ((lp.single 2 0 1 : Coeff 2), lp.single 2 0 1)
def lemma3_2CounterexampleParameter : ℂ := Complex.I / 10000

theorem lemma3_2Counterexample_off_lattice : lemma3_2CounterexampleParameter ∉ freeLattice := notMem_freeLattice_of_im_ne_zero (by norm_num [lemma3_2CounterexampleParameter])

/-- The exact squared input norm in the original Hilbert pair space. -/
theorem lemma3_2Counterexample_input_norm_sq : ‖lemma3_2CounterexampleInput‖^2 = 2 := by
  have h := norm_withLp_prod_rpow (p := 2) (by norm_num) lemma3_2CounterexampleInput
  norm_num [lemma3_2CounterexampleInput, Real.rpow_two] at h ⊢
  exact h

theorem lemma3_2Counterexample_input_norm : ‖lemma3_2CounterexampleInput‖ = Real.sqrt 2 := by
  rw [← lemma3_2Counterexample_input_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem lemma3_2Counterexample_input_norm_lt : ‖lemma3_2CounterexampleInput‖ < 3/2 := by
  nlinarith [lemma3_2Counterexample_input_norm_sq, norm_nonneg lemma3_2CounterexampleInput]

theorem lemma3_2Counterexample_output : sourceFreeResolventToL1 (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) lemma3_2CounterexampleParameter lemma3_2Counterexample_off_lattice lemma3_2CounterexampleInput =
    WithLp.toLp 1 ((lp.single 1 0 (1/lemma3_2CounterexampleParameter) : Coeff 1), lp.single 1 0 (1/lemma3_2CounterexampleParameter)) :=
  sourceFreeResolventToL1_diagonal_zero (by norm_num) _ _

theorem lemma3_2Counterexample_output_norm : ‖sourceFreeResolventToL1 (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) lemma3_2CounterexampleParameter lemma3_2Counterexample_off_lattice lemma3_2CounterexampleInput‖ = 20000 := by
  rw [lemma3_2Counterexample_output]
  change ‖(CoeffPair.toMax 1).symm (_, _)‖ = _
  rw [CoeffPair.norm_diagonal (by norm_num)]
  norm_num [lemma3_2CounterexampleParameter, norm_div]

theorem lemma3_2Counterexample_printed_rhs : (4*(2 : ℝ)/|lemma3_2CounterexampleParameter.im|^(1/(2 : ℝ)) + 1/|lemma3_2CounterexampleParameter.im|) = 10800 := by
  have hs : Real.sqrt (10000 : ℝ) = 100 := by
    rw [show (10000 : ℝ) = 100^2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [lemma3_2CounterexampleParameter, ← Real.sqrt_eq_rpow, hs]

theorem lemma3_2_printed_height_bound_false : 4*(2 : ℝ)/|lemma3_2CounterexampleParameter.im|^(1/(2 : ℝ)) + 1/|lemma3_2CounterexampleParameter.im| <
    ‖sourceFreeResolventToL1 (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) lemma3_2CounterexampleParameter lemma3_2Counterexample_off_lattice‖ := by
  rw [lemma3_2Counterexample_printed_rhs]
  have h := (sourceFreeResolventToL1 (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) lemma3_2CounterexampleParameter lemma3_2Counterexample_off_lattice).le_opNorm lemma3_2CounterexampleInput
  rw [lemma3_2Counterexample_output_norm] at h
  by_contra hc
  have hbound : ‖sourceFreeResolventToL1 (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) lemma3_2CounterexampleParameter lemma3_2Counterexample_off_lattice‖ ≤ 10800 := le_of_not_gt hc
  have hm := mul_le_mul hbound lemma3_2Counterexample_input_norm_lt.le (norm_nonneg lemma3_2CounterexampleInput) (by norm_num : (0 : ℝ) ≤ 10800)
  nlinarith

/-- The failure occurs off the free spectrum, with a nonzero imaginary part. -/
theorem not_lemma3_2_ii_original_norms :
    ¬ ∀ (z : ℂ) (hz : z ∉ freeLattice), z.im ≠ 0 →
      ‖sourceFreeResolventToL1 (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) z hz‖ ≤
        8/|z.im|^(1/(2 : ℝ)) + 1/|z.im| := by
  intro h
  have hb := h lemma3_2CounterexampleParameter lemma3_2Counterexample_off_lattice
    (by norm_num [lemma3_2CounterexampleParameter])
  have hf := lemma3_2_printed_height_bound_false
  norm_num at hb hf
  linarith

end NLS.ZakharovShabat
