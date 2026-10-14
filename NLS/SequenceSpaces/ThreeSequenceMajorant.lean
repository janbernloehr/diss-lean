import NLS.SequenceSpaces.SandwichMajorant

/-! # One sequence majorant from three common coordinate bounds -/

noncomputable section
namespace NLS.Coeff
open scoped ENNReal

theorem exists_common_majorant_of_three
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {J : Type*}
    (a b c : Coeff p) (L : ℝ) (hL : 0 ≤ L) (f : J → ℤ → ℂ)
    (hf : ∀ j m, ‖f j m‖ ≤ L*(‖a m‖+‖b m‖+‖c m‖)) :
    ∃ B : Coeff p, ‖B‖ ≤ L*(‖a‖+‖b‖+‖c‖) ∧ ∀ j m, ‖f j m‖ ≤ ‖B m‖ := by
  let A := magnitude a+magnitude b+magnitude c
  have hAn (m : ℤ) : ‖A m‖ = ‖a m‖+‖b m‖+‖c m‖ := by
    simp only [A,lp.coeFn_add,Pi.add_apply,magnitude_apply,← Complex.ofReal_add,Complex.norm_real]
    exact Real.norm_of_nonneg (by positivity)
  have hA : ‖A‖ ≤ ‖a‖+‖b‖+‖c‖ := by
    exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans_eq (by simp only [norm_magnitude]))
  let B : Coeff p := (L:ℂ) • A
  refine ⟨B,?_,?_⟩
  · simpa only [B,norm_smul,Complex.norm_real,Real.norm_of_nonneg hL] using mul_le_mul_of_nonneg_left hA hL
  · intro j m
    simpa only [B,lp.coeFn_smul,Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg hL,hAn] using hf j m

end NLS.Coeff
