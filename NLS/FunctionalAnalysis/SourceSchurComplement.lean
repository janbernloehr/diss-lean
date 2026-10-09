import NLS.FunctionalAnalysis.AnalyticSchurComplement
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Appendix I.1 and I.2 in the original identity-plus-operator convention

The lower block must be invertible before Schur elimination can be used.
The strict norm bound in I.2 supplies this hypothesis by the Neumann series.
-/
noncomputable section
namespace NLS.SchurComplement
variable {E F Z : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup Z] [NormedSpace ℂ Z]

/-- The source Schur complement, with the identity terms and printed signs. -/
def sourceSchur (A : E →L[ℂ] E) (B : F →L[ℂ] E) (C : E →L[ℂ] F) (D : F →L[ℂ] F) :
    E →L[ℂ] E := expression (1+A) B C (1+D)

@[simp] theorem sourceSchur_apply (A : E →L[ℂ] E) (B : F →L[ℂ] E)
    (C : E →L[ℂ] F) (D : F →L[ℂ] F) (x : E) :
    sourceSchur A B C D x = x+A x-B (Ring.inverse (1+D) (C x)) := rfl

/-- Adding the identity adds it to both diagonal blocks only. -/
theorem one_add_block (A : E →L[ℂ] E) (B : F →L[ℂ] E)
    (C : E →L[ℂ] F) (D : F →L[ℂ] F) :
    1+block A B C D = block (1+A) B C (1+D) := by
  ext <;> simp [block_apply,add_left_comm]

variable [CompleteSpace E] [CompleteSpace F]

/-- I.1 with its necessary lower-block hypothesis, without a finite-dimensional restriction. -/
theorem sourceLemmaI1_corrected (A : E →L[ℂ] E) (B : F →L[ℂ] E)
    (C : E →L[ℂ] F) (D : F →L[ℂ] F) (hD : IsUnit (1+D)) :
    IsUnit (1+block A B C D) ↔ IsUnit (sourceSchur A B C D) := by
  rw [one_add_block,sourceSchur]
  generalize he : 1+D = L at *
  obtain ⟨u,rfl⟩ := hD
  rw [ContinuousLinearMap.isUnit_iff_bijective,ContinuousLinearMap.isUnit_iff_bijective]
  have h := bijective_block_iff (1+A) B C (ContinuousLinearEquiv.ofUnit u)
  change Function.Bijective (block (1+A) B C (u : F →L[ℂ] F)) ↔ _ at h
  rw [h]
  simp only [expression,schur,Ring.inverse_unit]
  rfl

/-- The sufficient direction of the printed I.1 remains valid. -/
theorem sourceLemmaI1_sufficient (A : E →L[ℂ] E) (B : F →L[ℂ] E)
    (C : E →L[ℂ] F) (D : F →L[ℂ] F)
    (hD : IsUnit (1+D)) (hS : IsUnit (sourceSchur A B C D)) :
    IsUnit (1+block A B C D) := (sourceLemmaI1_corrected A B C D hD).mpr hS

/-- The source's strict norm bound supplies a bounded inverse for the lower block. -/
theorem source_lower_isUnit_of_norm_lt_one (D : F →L[ℂ] F) (hD : ‖D‖ < 1) :
    IsUnit (1+D) := by
  simpa only [sub_neg_eq_add] using
    (isUnit_one_sub_of_norm_lt_one (x := -D) (by simpa only [norm_neg] using hD))

omit [CompleteSpace E] in
/-- I.2, in fact as an equivalence once its strict norm bound is fixed. -/
theorem sourceCorollaryI2_iff [FiniteDimensional ℂ E]
    (A : E →L[ℂ] E) (B : F →L[ℂ] E) (C : E →L[ℂ] F) (D : F →L[ℂ] F)
    (hD : ‖D‖ < 1) :
    IsUnit (1+block A B C D) ↔ (sourceSchur A B C D).toLinearMap.det ≠ 0 := by
  rw [one_add_block]
  exact isUnit_block_iff_det_ne_zero (1+A) B C (1+D) (source_lower_isUnit_of_norm_lt_one D hD)

omit [CompleteSpace E] in
/-- The printed sufficient condition uses precisely det S ≠ 0 and ‖D‖ < 1. -/
theorem sourceCorollaryI2 [FiniteDimensional ℂ E]
    (A : E →L[ℂ] E) (B : F →L[ℂ] E) (C : E →L[ℂ] F) (D : F →L[ℂ] F)
    (hS : (sourceSchur A B C D).toLinearMap.det ≠ 0) (hD : ‖D‖ < 1) :
    IsUnit (1+block A B C D) := (sourceCorollaryI2_iff A B C D hD).mpr hS

variable [CompleteSpace Z]

/-- Transfer from an actual topological direct-sum decomposition of the original space. -/
theorem source_operator_isUnit_iff (e : Z ≃L[ℂ] E × F) (T : Z →L[ℂ] Z)
    (A : E →L[ℂ] E) (B : F →L[ℂ] E) (C : E →L[ℂ] F) (D : F →L[ℂ] F)
    (hT : ∀ z, e (T z) = block A B C D (e z)) :
    IsUnit (1+T) ↔ IsUnit (1+block A B C D) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective,ContinuousLinearMap.isUnit_iff_bijective]
  have he : e ∘ (1+T : Z →L[ℂ] Z) = (1+block A B C D : E × F →L[ℂ] E × F) ∘ e := by
    funext z
    simp only [Function.comp_apply,add_apply,one_apply_eq_self,map_add,hT]
  have hl := Function.Bijective.of_comp_iff' e.bijective (1+T : Z →L[ℂ] Z)
  rw [he] at hl
  exact hl.symm.trans (Function.Bijective.of_comp_iff _ e.bijective)

/-- Corrected I.1 on the original Banach space, in any bounded direct-sum coordinates. -/
theorem sourceLemmaI1_on_decomposition (e : Z ≃L[ℂ] E × F) (T : Z →L[ℂ] Z)
    (A : E →L[ℂ] E) (B : F →L[ℂ] E) (C : E →L[ℂ] F) (D : F →L[ℂ] F)
    (hT : ∀ z, e (T z) = block A B C D (e z)) (hD : IsUnit (1+D)) :
    IsUnit (1+T) ↔ IsUnit (sourceSchur A B C D) :=
  (source_operator_isUnit_iff e T A B C D hT).trans (sourceLemmaI1_corrected A B C D hD)

omit [CompleteSpace E] in
/-- I.2 on the source Banach space itself, not just on an external product. -/
theorem sourceCorollaryI2_on_decomposition [FiniteDimensional ℂ E]
    (e : Z ≃L[ℂ] E × F) (T : Z →L[ℂ] Z)
    (A : E →L[ℂ] E) (B : F →L[ℂ] E) (C : E →L[ℂ] F) (D : F →L[ℂ] F)
    (hT : ∀ z, e (T z) = block A B C D (e z))
    (hS : (sourceSchur A B C D).toLinearMap.det ≠ 0) (hD : ‖D‖ < 1) :
    IsUnit (1+T) :=
  (source_operator_isUnit_iff e T A B C D hT).mpr (sourceCorollaryI2 A B C D hS hD)

end NLS.SchurComplement
