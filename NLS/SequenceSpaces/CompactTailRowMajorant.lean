import NLS.SequenceSpaces.CompactRowMajorant
import NLS.SequenceSpaces.FiniteModification
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Compactness from a tail row majorant

A bounded operator has only finitely many output rows outside any
two-sided index tail. The operator norm bounds those finite rows, so
an `ℓᵖ` majorant on the tail suffices for compactness without separate
finite-head estimates.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A deleted-coordinate operator is compact if its distant output
rows have one `ℓᵖ` row majorant. Finite head rows are patched with the
operator norm. -/
theorem isCompactOperator_deleted_of_tailRowMajorant
    (hp : p ≠ ⊤) (n : ℤ)
    (T : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (b : Coeff p) (K : ℕ)
    (htail : ∀ m : ℤ, K ≤ m.natAbs →
      ∀ a : DeletedCoeff p n,
        ‖((T a : DeletedCoeff p n) : Coeff p) m‖ ≤
          ‖b m‖ * ‖a‖) :
    IsCompactOperator T := by
  classical
  let s : Finset ℤ := Finset.Icc (-(K : ℤ)) (K : ℤ)
  let b' : Coeff p :=
    ⟨fun m => if m ∈ s then (‖T‖ : ℂ) else b m,
      memℓp_of_eq_outside_finset (lp.memℓp b) s (by
        intro m hm
        simp only [if_neg hm])⟩
  apply isCompactOperator_deleted_of_rowMajorant hp n T b'
  intro m a
  by_cases hm : m ∈ s
  · have heval : ‖((T a : DeletedCoeff p n) : Coeff p) m‖ ≤ ‖T a‖ :=
      lp.norm_apply_le_norm (zero_lt_one.trans_le Fact.out).ne' _ m
    have hop : ‖T a‖ ≤ ‖T‖ * ‖a‖ := T.le_opNorm a
    have hb' : ‖b' m‖ = ‖T‖ := by
      simp [b',hm,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg T)]
    rw [hb']
    exact heval.trans hop
  · have hmTail : K ≤ m.natAbs := by
      simp only [s,Finset.mem_Icc] at hm
      omega
    have hb' : b' m = b m := by simp [b',hm]
    rw [hb']
    exact htail m hmTail a

end NLS.Coeff
