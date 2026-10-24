import NLS.FunctionalAnalysis.SelfAdjointCayley

/-! # Eigenvectors of the actual Cayley transform -/
noncomputable section
set_option autoImplicit false
open Complex
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {T : E →ₗ.[ℂ] E}

/-- If the self-adjoint partial operator has no nonzero eigenvectors in its
actual domain, neither does its bounded Cayley transform. -/
theorem selfAdjointCayley_eigenvector_eq_zero (hT : IsSelfAdjoint T)
    (hno : ∀ (z : ℂ) (y : T.domain), T y = z • (y : E) → (y : E) = 0)
    (ζ : ℂ) (f : E) (heig : selfAdjointCayley hT f = ζ • f) : f = 0 := by
  by_cases hζ : ζ = 1
  · apply (selfAdjointCayley_apply_eq_self_iff hT f).mp
    simpa [hζ] using heig
  have hn : ζ-1 ≠ 0 := sub_ne_zero.mpr hζ
  let y := selfAdjointNonrealResolventToDomain hT (-I) (by simp) f
  have he : (ζ-1) • f = (2*I) • (y : E) := by
    change f+(2*I) • (y : E) = ζ • f at heig
    calc
      (ζ-1) • f = ζ • f-f := by module
      _ = (f+(2*I) • (y : E))-f := by rw [heig]
      _ = _ := by module
  have hf : f = ((ζ-1)⁻¹*(2*I)) • (y : E) := by
    calc
      f = (ζ-1)⁻¹ • ((ζ-1) • f) := by rw [smul_smul,inv_mul_cancel₀ hn,one_smul]
      _ = _ := by rw [he,smul_smul]
  have hy := linearPMapPencil_selfAdjointNonrealResolventToDomain hT (-I) (by simp) f
  change -I • (y : E)-T y = f at hy
  have hyEig : T y = (-I-((ζ-1)⁻¹*(2*I))) • (y : E) := by
    calc
      T y = -I • (y : E)-(-I • (y : E)-T y) := by module
      _ = -I • (y : E)-f := by rw [hy]
      _ = _ := by rw [hf]; module
  have hy0 := hno _ y hyEig
  rw [hf,hy0,smul_zero]

end NLS.FunctionalAnalysis
