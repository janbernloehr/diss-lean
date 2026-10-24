import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! # A symmetric adjoint of a dense symmetric operator is self-adjoint -/
noncomputable section
set_option autoImplicit false
open Set
namespace NLS.FunctionalAnalysis

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The actual adjoint reverses inclusion of densely defined operators. -/
theorem adjoint_le_adjoint_of_le {T S : E →ₗ.[𝕜] F}
    (hT : Dense (T.domain : Set E)) (hS : Dense (S.domain : Set E)) (hTS : T ≤ S) :
    S.adjoint ≤ T.adjoint := by
  apply LinearPMap.IsFormalAdjoint.le_adjoint hT
  intro x y
  let z : S.domain := ⟨x,hTS.1 x.property⟩
  have he : T x = S z := hTS.2 (show (x : E) = (z : E) from rfl)
  rw [he]
  exact (LinearPMap.adjoint_isFormalAdjoint hS).symm z y

/-- Symmetry of both a dense operator and its actual adjoint implies
self-adjointness of that adjoint. -/
theorem isSelfAdjoint_adjoint_of_symmetric_adjoint {T : E →ₗ.[𝕜] E}
    (hT : Dense (T.domain : Set E)) (hs : T.IsFormalAdjoint T)
    (ha : T.adjoint.IsFormalAdjoint T.adjoint) : IsSelfAdjoint T.adjoint := by
  have hle : T ≤ T.adjoint := hs.le_adjoint hT
  have hd : Dense (T.adjoint.domain : Set E) := hT.mono hle.1
  rw [LinearPMap.isSelfAdjoint_def]
  exact le_antisymm (adjoint_le_adjoint_of_le hT hd hle) (ha.le_adjoint hd)

end NLS.FunctionalAnalysis
