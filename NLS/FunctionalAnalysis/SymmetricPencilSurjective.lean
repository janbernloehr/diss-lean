import NLS.FunctionalAnalysis.SymmetricPencilEstimate

/-! # A surjective real symmetric pencil is injective -/
noncomputable section
set_option autoImplicit false
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Symmetry gives the actual real pencil its own formal adjoint pairing. -/
theorem inner_linearPMapPencil_left (T : E →ₗ.[ℂ] E) (hs : T.IsFormalAdjoint T)
    (z : ℂ) (hz : z.im = 0) (x y : T.domain) :
    inner ℂ (linearPMapPencil T z x) (y : E) =
      inner ℂ (x : E) (linearPMapPencil T z y) := by
  have hstar : (starRingEnd ℂ) z = z := by
    apply Complex.ext <;> simp [hz]
  simp only [linearPMapPencil_apply,inner_sub_left,inner_sub_right,
    inner_smul_left,inner_smul_right,hstar,hs x y]

/-- Surjectivity of a real symmetric pencil rules out a kernel. This is
useful when an explicit bounded Green operator first gives a right inverse. -/
theorem linearPMapPencil_injective_of_surjective_real (T : E →ₗ.[ℂ] E)
    (hs : T.IsFormalAdjoint T) (z : ℂ) (hz : z.im = 0)
    (hsurj : Function.Surjective (linearPMapPencil T z)) :
    Function.Injective (linearPMapPencil T z) := by
  have hker (x : T.domain) (hx : linearPMapPencil T z x = 0) : x = 0 := by
    obtain ⟨y,hy⟩ := hsurj (x : E)
    have h := inner_linearPMapPencil_left T hs z hz y x
    rw [hy,hx,inner_zero_right] at h
    apply Subtype.ext
    exact inner_self_eq_zero.mp h
  intro x y hxy
  apply sub_eq_zero.mp
  exact hker (x-y) (by rw [map_sub,hxy,sub_self])

end NLS.FunctionalAnalysis
