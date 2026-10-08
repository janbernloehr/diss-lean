import NLS.SequenceSpaces.Basic

/-! # Literal coordinate norm suprema dominated by a sequence majorant -/
noncomputable section
open scoped ENNReal
namespace NLS

/-- A common coefficient majorant bounds the literal suprema, at every positive exponent. -/
theorem exists_coordinateNormSup {X : Type*} {p : ℝ≥0∞} (hp : p ≠ 0)
    (D : ℤ → Set X) (hD : ∀ n, (D n).Nonempty) (F : ℤ → X → ℂ)
    (b : Coeff p) (hmajor : ∀ n, ∀ x ∈ D n, ‖F n x‖ ≤ ‖b n‖) :
    ∃ B : Coeff p,
      (∀ n, B n = ((sSup ((fun x => ‖F n x‖) '' D n):ℝ):ℂ)) ∧
      (∀ n, ∀ x ∈ D n, ‖F n x‖ ≤ ‖B n‖) ∧ ‖B‖ ≤ ‖b‖ := by
  let U (n : ℤ) : Set ℝ := (fun x => ‖F n x‖) '' D n
  have hne (n : ℤ) : (U n).Nonempty := (hD n).image _
  have hupper (n : ℤ) : ∀ u ∈ U n, u ≤ ‖b n‖ := by
    rintro u ⟨x,hx,rfl⟩
    exact hmajor n x hx
  have hbdd (n : ℤ) : BddAbove (U n) := ⟨_,hupper n⟩
  have hnonneg (n : ℤ) : 0 ≤ sSup (U n) := by
    obtain ⟨x,hx⟩ := hD n
    exact (norm_nonneg _).trans (le_csSup (hbdd n) ⟨x,hx,rfl⟩)
  have hdom (n : ℤ) : ‖((sSup (U n):ℝ):ℂ)‖ ≤ ‖b n‖ := by
    rw [Complex.norm_real,Real.norm_of_nonneg (hnonneg n)]
    exact csSup_le (hne n) (hupper n)
  let B : Coeff p := ⟨fun n => ((sSup (U n):ℝ):ℂ),(lp.memℓp b).mono' hdom⟩
  refine ⟨B,fun _ => rfl,?_,lp.norm_mono hp hdom⟩
  intro n x hx
  change ‖F n x‖ ≤ ‖((sSup (U n):ℝ):ℂ)‖
  rw [Complex.norm_real,Real.norm_of_nonneg (hnonneg n)]
  exact le_csSup (hbdd n) ⟨x,hx,rfl⟩

end NLS
