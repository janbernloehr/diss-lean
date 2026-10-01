import NLS.ZakharovShabat.SourceRealTypeBanachSpace
import NLS.ZakharovShabat.SourceRealTypeDecomposition

/-! # The bounded real projection onto the actual source real form

The previously constructed real part is real linear and continuous, so
it is a bounded projection into the closed real-type Banach subspace.
It fixes actual real sources. This lets an ambient analytic vector field
that preserves reality be treated as a differentiable real Banach-space
vector field, with the same actual source values.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual source real-part projection, with its closed real
Banach subspace as codomain. -/
def sourceRealTypeProjection (hp : p ≠ ⊤) :
    CoeffPair p →L[ℝ] realTypeSourceSubmodule p where
  toFun u := ⟨sourceRealPart u,sourceRealPart_realType u⟩
  map_add' u v := by
    apply Subtype.ext
    change sourceRealPart (u+v) = sourceRealPart u+sourceRealPart v
    simp only [sourceRealPart,sourceConjugation_add]
    module
  map_smul' r u := by
    apply Subtype.ext
    change sourceRealPart ((r:ℂ) • u) = (r:ℂ) • sourceRealPart u
    simp only [sourceRealPart,sourceConjugation_smul,Complex.conj_ofReal]
    module
  cont := (continuous_sourceRealPart hp).subtype_mk _

@[simp] theorem sourceRealTypeProjection_val (hp : p ≠ ⊤) (u : CoeffPair p) :
    (sourceRealTypeProjection hp u : CoeffPair p) = sourceRealPart u := rfl

/-- The projection has exactly the original source value on the real form. -/
theorem sourceRealTypeProjection_val_of_realType
    (hp : p ≠ ⊤) (u : CoeffPair p) (hu : IsRealType (CoeffPair.toMax p u)) :
    (sourceRealTypeProjection hp u : CoeffPair p) = u := by
  rw [sourceRealTypeProjection_val,sourceRealPart,(sourceConjugation_fixed_iff u).mpr hu]
  module

@[simp] theorem sourceRealTypeProjection_subtype (hp : p ≠ ⊤) (u : realTypeSourceSubmodule p) :
    sourceRealTypeProjection hp (u : CoeffPair p) = u := by
  apply Subtype.ext
  exact sourceRealTypeProjection_val_of_realType hp u.val u.property

end NLS.ZakharovShabat
