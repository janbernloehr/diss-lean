import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! # Nonreal spectral-pencil estimates for symmetric partial operators

These are estimates for the actual unbounded operator domain. They give
injectivity and inverse bounds on the range, without assuming surjectivity.
-/
noncomputable section
set_option autoImplicit false
namespace NLS.FunctionalAnalysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The original spectral pencil on the actual partial-operator domain. -/
def linearPMapPencil (T : E →ₗ.[ℂ] E) (z : ℂ) : T.domain →ₗ[ℂ] E :=
  z • T.domain.subtype - T.toFun

@[simp] theorem linearPMapPencil_apply (T : E →ₗ.[ℂ] E) (z : ℂ) (x : T.domain) :
    linearPMapPencil T z x = z • (x : E) - T x := rfl

/-- The diagonal pairing of a symmetric partial operator is real. -/
theorem inner_apply_im_eq_zero_of_formal_symmetric {T : E →ₗ.[ℂ] E}
    (hs : T.IsFormalAdjoint T) (x : T.domain) : (inner ℂ (x : E) (T x)).im = 0 := by
  have h := congrArg Complex.im (hs x x)
  have hi := inner_im_symm (𝕜 := ℂ) (T x) (x : E)
  change (inner ℂ (T x) (x : E)).im = -(inner ℂ (x : E) (T x)).im at hi
  linarith

/-- The imaginary part gives a lower bound independent of the real part
of the spectral parameter. -/
theorem norm_linearPMapPencil_ge_im {T : E →ₗ.[ℂ] E}
    (hs : T.IsFormalAdjoint T) (z : ℂ) (x : T.domain) :
    |z.im| * ‖(x : E)‖ ≤ ‖linearPMapPencil T z x‖ := by
  have him : (inner ℂ (x : E) (linearPMapPencil T z x)).im = z.im * ‖(x : E)‖ ^ 2 := by
    rw [linearPMapPencil_apply,inner_sub_right,inner_smul_right,Complex.sub_im,
      inner_apply_im_eq_zero_of_formal_symmetric hs x,sub_zero,
      inner_self_eq_norm_sq_to_K]
    change (z * ((‖(x : E)‖ : ℂ) ^ 2)).im = _
    simp [pow_two,Complex.mul_re,Complex.mul_im]
  have hb : |z.im| * ‖(x : E)‖ ^ 2 ≤ ‖(x : E)‖ * ‖linearPMapPencil T z x‖ := by
    calc
      _ = |(inner ℂ (x : E) (linearPMapPencil T z x)).im| := by
        rw [him,abs_mul]
        simp only [abs_pow,abs_norm]
      _ ≤ ‖inner ℂ (x : E) (linearPMapPencil T z x)‖ := Complex.abs_im_le_norm _
      _ ≤ _ := norm_inner_le_norm _ _
  by_cases hx : (x : E) = 0
  · simp [hx]
  · have hp : 0 < ‖(x : E)‖ := norm_pos_iff.mpr hx
    nlinarith [hb]

/-- At a nonreal parameter the original pencil is injective. -/
theorem linearPMapPencil_injective_of_im_ne_zero {T : E →ₗ.[ℂ] E}
    (hs : T.IsFormalAdjoint T) (z : ℂ) (hz : z.im ≠ 0) :
    Function.Injective (linearPMapPencil T z) := by
  intro x y h
  have he : linearPMapPencil T z (x-y) = 0 := by rw [map_sub,h,sub_self]
  have hb := norm_linearPMapPencil_ge_im hs z (x-y)
  rw [he,norm_zero] at hb
  have hn : ‖((x-y : T.domain) : E)‖ = 0 := by
    have hp : 0 < |z.im| := abs_pos.mpr hz
    have hnon := norm_nonneg ((x-y : T.domain) : E)
    nlinarith
  apply sub_eq_zero.mp
  apply Subtype.ext
  exact norm_eq_zero.mp hn

/-- The inverse estimate holds for every vector in the actual domain. -/
theorem norm_le_linearPMapPencil_div_im {T : E →ₗ.[ℂ] E}
    (hs : T.IsFormalAdjoint T) (z : ℂ) (hz : z.im ≠ 0) (x : T.domain) :
    ‖(x : E)‖ ≤ ‖linearPMapPencil T z x‖ / |z.im| := by
  apply (le_div_iff₀ (abs_pos.mpr hz)).mpr
  simpa only [mul_comm] using norm_linearPMapPencil_ge_im hs z x

end NLS.FunctionalAnalysis
