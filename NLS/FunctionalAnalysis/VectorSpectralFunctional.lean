import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-! # Positive vector functionals from an actual continuous functional calculus -/
noncomputable section
set_option autoImplicit false
open scoped CompactlySupported
open Complex
namespace NLS.FunctionalAnalysis
variable {X E : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Complexification of a compactly supported real continuous test function. -/
def complexifyCompactFunction (f : C_c(X, ℝ)) : C(X, ℂ) :=
  ⟨fun x => (f x : ℂ), continuous_ofReal.comp f.continuous⟩

@[simp] theorem complexifyCompactFunction_apply (f : C_c(X, ℝ)) (x : X) :
    complexifyCompactFunction f x = (f x : ℂ) := rfl

@[simp] theorem complexifyCompactFunction_add (f g : C_c(X, ℝ)) :
    complexifyCompactFunction (f+g) = complexifyCompactFunction f+complexifyCompactFunction g := by
  ext x
  simp [complexifyCompactFunction]

@[simp] theorem complexifyCompactFunction_smul (r : ℝ) (f : C_c(X, ℝ)) :
    complexifyCompactFunction (r • f) = (r : ℂ) • complexifyCompactFunction f := by
  ext x
  simp [complexifyCompactFunction]

/-- Positivity of the vector functional follows from a continuous square root,
the star homomorphism, and the actual Hilbert adjoint. -/
theorem re_inner_complexify_nonneg (Φ : C(X, ℂ) →⋆ₐ[ℂ] (E →L[ℂ] E))
    (v : E) (f : C_c(X, ℝ)) (hf : 0 ≤ f) :
    0 ≤ (inner ℂ v (Φ (complexifyCompactFunction f) v)).re := by
  let g : C(X, ℂ) := ⟨fun x => (Real.sqrt (f x) : ℂ),
    continuous_ofReal.comp (Real.continuous_sqrt.comp f.continuous)⟩
  have hfac : complexifyCompactFunction f = star g*g := by
    ext x
    change (f x : ℂ) = star (Real.sqrt (f x) : ℂ)*(Real.sqrt (f x) : ℂ)
    simp only [star_def,conj_ofReal,← ofReal_mul]
    exact congrArg ofReal (Real.mul_self_sqrt (hf x)).symm
  rw [hfac,map_mul,map_star]
  change 0 ≤ (inner ℂ v (ContinuousLinearMap.adjoint (Φ g) (Φ g v))).re
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact inner_self_nonneg (𝕜 := ℂ) (x := Φ g v)

/-- The positive real vector functional associated with an actual star-algebra
homomorphism into bounded Hilbert-space operators. -/
def vectorPositiveFunctional (Φ : C(X, ℂ) →⋆ₐ[ℂ] (E →L[ℂ] E)) (v : E) :
    C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => (inner ℂ v (Φ (complexifyCompactFunction f) v)).re
      map_add' := by
        intro f g
        simp [inner_add_right]
      map_smul' := by
        intro r f
        simp only [complexifyCompactFunction_smul,map_smul,smul_apply,inner_smul_right]
        simp }
    (re_inner_complexify_nonneg Φ v)

@[simp] theorem vectorPositiveFunctional_apply
    (Φ : C(X, ℂ) →⋆ₐ[ℂ] (E →L[ℂ] E)) (v : E) (f : C_c(X, ℝ)) :
    vectorPositiveFunctional Φ v f = (inner ℂ v (Φ (complexifyCompactFunction f) v)).re := rfl

end NLS.FunctionalAnalysis
