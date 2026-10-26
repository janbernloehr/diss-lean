import NLS.FunctionalAnalysis.SymmetricPencilEstimate

/-! # Self-adjointness from two surjective conjugate pencils -/
noncomputable section
set_option autoImplicit false
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Surjectivity of the conjugate pencil annihilates the kernel of the actual adjoint pencil. -/
theorem adjoint_pencil_injective_of_conjugate_surjective (T : E →ₗ.[ℂ] E)
    (hT : Dense (T.domain : Set E)) (z : ℂ)
    (h : Function.Surjective (linearPMapPencil T (star z))) :
    Function.Injective (linearPMapPencil T.adjoint z) := by
  have hzero (y : T.adjoint.domain) (hy : linearPMapPencil T.adjoint z y = 0) : y = 0 := by
    have he : T.adjoint y = z • (y : E) := by
      exact (sub_eq_zero.mp hy).symm
    have hi (x : T.domain) : inner ℂ (linearPMapPencil T (star z) x) (y : E) = 0 := by
      rw [linearPMapPencil_apply,inner_sub_left,inner_smul_left,
        (LinearPMap.adjoint_isFormalAdjoint hT).symm x y,he,inner_smul_right]
      simp
    obtain ⟨x,hx⟩ := h (y : E)
    have hy0 : (y : E) = 0 := inner_self_eq_zero.mp (by simpa only [hx] using hi x)
    exact Subtype.ext hy0
  intro x y hxy
  apply sub_eq_zero.mp
  exact hzero (x-y) (by rw [map_sub,hxy,sub_self])

/-- A dense symmetric operator is self-adjoint if its pencils at a conjugate
pair of parameters are both surjective. The domain equality is proved, not assumed. -/
theorem isSelfAdjoint_of_conjugate_pencils_surjective (T : E →ₗ.[ℂ] E)
    (hT : Dense (T.domain : Set E)) (hs : T.IsFormalAdjoint T) (z : ℂ)
    (hz : Function.Surjective (linearPMapPencil T z))
    (hzbar : Function.Surjective (linearPMapPencil T (star z))) : IsSelfAdjoint T := by
  have hle : T ≤ T.adjoint := hs.le_adjoint hT
  have hinj := adjoint_pencil_injective_of_conjugate_surjective T hT z hzbar
  have hdom : T.adjoint.domain ≤ T.domain := by
    intro y hy
    let ya : T.adjoint.domain := ⟨y,hy⟩
    obtain ⟨x,hx⟩ := hz (linearPMapPencil T.adjoint z ya)
    let xa : T.adjoint.domain := ⟨x,hle.1 x.property⟩
    have ha : T.adjoint xa = T x := (hle.2 (show (x : E) = (xa : E) from rfl)).symm
    have hp : linearPMapPencil T.adjoint z xa = linearPMapPencil T.adjoint z ya := by
      rw [linearPMapPencil_apply,ha]
      exact hx
    have he : (x : E) = y := congrArg Subtype.val (hinj hp)
    exact he ▸ x.property
  rw [LinearPMap.isSelfAdjoint_def]
  exact (LinearPMap.eq_of_le_of_domain_eq hle (le_antisymm hle.1 hdom)).symm

end NLS.FunctionalAnalysis
