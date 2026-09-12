import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith

/-!
# Complementary graphs of a linear isometry

For a linear isometry equivalence `J`, the graphs `(J a, a)` and `(-J b, b)`
are closed complementary subspaces. Their coordinate projections are contractive
in the maximum product norm. Applied to frequency reflection, they describe
the Dirichlet and Neumann Fourier spaces of Chapter 1, §4.
-/

noncomputable section
namespace NLS.ReflectionSplit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (J : E ≃ₗᵢ[ℂ] E)

/-- The positive graph `(J a, a)`. -/
def positive : Submodule ℂ (E × E) :=
  (ContinuousLinearMap.fst ℂ E E -
    J.toContinuousLinearEquiv.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℂ E E)).ker

/-- The negative graph `(-J b, b)`. -/
def negative : Submodule ℂ (E × E) :=
  (ContinuousLinearMap.fst ℂ E E +
    J.toContinuousLinearEquiv.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℂ E E)).ker

@[simp] theorem mem_positive (x : E × E) : x ∈ positive J ↔ x.1 = J x.2 := by
  change x.1 - J x.2 = 0 ↔ _
  exact sub_eq_zero

@[simp] theorem mem_negative (x : E × E) : x ∈ negative J ↔ x.1 = -J x.2 := by
  change x.1 + J x.2 = 0 ↔ _
  exact eq_neg_iff_add_eq_zero.symm

theorem isClosed_positive : IsClosed (positive J : Set (E × E)) :=
  ContinuousLinearMap.isClosed_ker _

theorem isClosed_negative : IsClosed (negative J : Set (E × E)) :=
  ContinuousLinearMap.isClosed_ker _

/-- Include the amplitude in the positive graph. -/
def positiveEmbedding : E →L[ℂ] E × E :=
  J.toContinuousLinearEquiv.toContinuousLinearMap.prod (ContinuousLinearMap.id ℂ E)

/-- Include the amplitude in the negative graph. -/
def negativeEmbedding : E →L[ℂ] E × E :=
  (-J.toContinuousLinearEquiv.toContinuousLinearMap).prod (ContinuousLinearMap.id ℂ E)

@[simp] theorem positiveEmbedding_apply (a : E) : positiveEmbedding J a = (J a, a) := rfl
@[simp] theorem negativeEmbedding_apply (a : E) : negativeEmbedding J a = (-J a, a) := rfl

@[simp] theorem norm_positiveEmbedding (a : E) : ‖positiveEmbedding J a‖ = ‖a‖ := by
  simp [Prod.norm_def]

@[simp] theorem norm_negativeEmbedding (a : E) : ‖negativeEmbedding J a‖ = ‖a‖ := by
  simp [Prod.norm_def]

/-- The positive graph has exactly the scalar amplitude norm. -/
def positiveEquivalence : E ≃ₗᵢ[ℂ] ↥(positive J) where
  toFun a := ⟨positiveEmbedding J a, by simp⟩
  invFun x := x.val.2
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    exact Prod.ext ((mem_positive J x.val).mp x.property).symm rfl
  map_add' _ _ := by apply Subtype.ext; exact map_add (positiveEmbedding J) _ _
  map_smul' _ _ := by apply Subtype.ext; exact map_smul (positiveEmbedding J) _ _
  norm_map' := norm_positiveEmbedding J

/-- The negative graph has exactly the scalar amplitude norm. -/
def negativeEquivalence : E ≃ₗᵢ[ℂ] ↥(negative J) where
  toFun a := ⟨negativeEmbedding J a, by simp⟩
  invFun x := x.val.2
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    exact Prod.ext ((mem_negative J x.val).mp x.property).symm rfl
  map_add' _ _ := by apply Subtype.ext; exact map_add (negativeEmbedding J) _ _
  map_smul' _ _ := by apply Subtype.ext; exact map_smul (negativeEmbedding J) _ _
  norm_map' := norm_negativeEmbedding J

/-- Positive amplitude of an arbitrary pair. -/
def positiveAmplitude : (E × E) →L[ℂ] E :=
  (2 : ℂ)⁻¹ • (J.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ContinuousLinearMap.fst ℂ E E) + ContinuousLinearMap.snd ℂ E E)

/-- Negative amplitude of an arbitrary pair. -/
def negativeAmplitude : (E × E) →L[ℂ] E :=
  (2 : ℂ)⁻¹ • (ContinuousLinearMap.snd ℂ E E -
    J.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℂ E E))

@[simp] theorem positiveAmplitude_apply (x : E × E) :
    positiveAmplitude J x = (2 : ℂ)⁻¹ • (J.symm x.1 + x.2) := rfl
@[simp] theorem negativeAmplitude_apply (x : E × E) :
    negativeAmplitude J x = (2 : ℂ)⁻¹ • (x.2 - J.symm x.1) := rfl

/-- The projection onto the positive graph along the negative graph. -/
def positiveProjection : (E × E) →L[ℂ] E × E :=
  (positiveEmbedding J).comp (positiveAmplitude J)

/-- The projection onto the negative graph along the positive graph. -/
def negativeProjection : (E × E) →L[ℂ] E × E :=
  (negativeEmbedding J).comp (negativeAmplitude J)

theorem positiveProjection_mem (x : E × E) : positiveProjection J x ∈ positive J := by
  simp [positiveProjection]

theorem negativeProjection_mem (x : E × E) : negativeProjection J x ∈ negative J := by
  simp [negativeProjection]
  module

/-- Every pair is the sum of its two reflected components. -/
theorem decomposition (x : E × E) : positiveProjection J x + negativeProjection J x = x := by
  apply Prod.ext <;>
    simp [positiveProjection, negativeProjection, map_smul, map_add, map_sub] <;> module

theorem disjoint : Disjoint (positive J) (negative J) := by
  rw [Submodule.disjoint_def]
  intro x hp hn
  rw [mem_positive] at hp
  rw [mem_negative] at hn
  have hh : (2 : ℂ) • J x.2 = 0 := by
    calc
      _ = J x.2 + J x.2 := by module
      _ = 0 := by nth_rw 1 [← hp]; rw [hn, neg_add_cancel]
  have h : J x.2 = 0 := (smul_eq_zero.mp hh).resolve_left (by norm_num)
  have h₂ : x.2 = 0 := J.injective (by simpa using h)
  exact Prod.ext (by simpa [h₂] using hp) h₂

theorem isCompl : IsCompl (positive J) (negative J) := by
  refine ⟨disjoint J, ?_⟩
  rw [codisjoint_iff, eq_top_iff]
  intro x _
  rw [← decomposition J x]
  exact Submodule.add_mem_sup (positiveProjection_mem J x) (negativeProjection_mem J x)

theorem positiveProjection_eq_self {x : E × E} (hx : x ∈ positive J) :
    positiveProjection J x = x := by
  rw [mem_positive] at hx
  apply Prod.ext <;> simp [positiveProjection, hx, map_smul, map_add] <;> module

theorem negativeProjection_eq_self {x : E × E} (hx : x ∈ negative J) :
    negativeProjection J x = x := by
  rw [mem_negative] at hx
  apply Prod.ext <;> simp [negativeProjection, hx, map_smul] <;> module

theorem positiveProjection_idempotent : IsIdempotentElem (positiveProjection J) := by
  apply ContinuousLinearMap.ext
  intro x
  exact positiveProjection_eq_self J (positiveProjection_mem J x)

theorem negativeProjection_idempotent : IsIdempotentElem (negativeProjection J) := by
  apply ContinuousLinearMap.ext
  intro x
  exact negativeProjection_eq_self J (negativeProjection_mem J x)

theorem positiveProjection_eq_zero {x : E × E} (hx : x ∈ negative J) :
    positiveProjection J x = 0 := by
  have h := decomposition J x
  rw [negativeProjection_eq_self J hx] at h
  simpa using h

theorem negativeProjection_eq_zero {x : E × E} (hx : x ∈ positive J) :
    negativeProjection J x = 0 := by
  have h := decomposition J x
  rw [positiveProjection_eq_self J hx] at h
  simpa using h

theorem norm_positiveProjection_le (x : E × E) : ‖positiveProjection J x‖ ≤ ‖x‖ := by
  change ‖positiveEmbedding J (positiveAmplitude J x)‖ ≤ _
  rw [norm_positiveEmbedding, positiveAmplitude_apply, norm_smul]
  have h : ‖J.symm x.1 + x.2‖ ≤ 2 * ‖x‖ :=
    (norm_add_le _ _).trans (by simpa [two_mul] using add_le_add (norm_fst_le x) (norm_snd_le x))
  norm_num at ⊢
  linarith

theorem norm_negativeProjection_le (x : E × E) : ‖negativeProjection J x‖ ≤ ‖x‖ := by
  change ‖negativeEmbedding J (negativeAmplitude J x)‖ ≤ _
  rw [norm_negativeEmbedding, negativeAmplitude_apply, norm_smul]
  have h : ‖x.2 - J.symm x.1‖ ≤ 2 * ‖x‖ :=
    (norm_sub_le _ _).trans (by simpa [two_mul] using add_le_add (norm_snd_le x) (norm_fst_le x))
  norm_num at ⊢
  linarith

end NLS.ReflectionSplit
