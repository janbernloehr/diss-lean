import NLS.ZakharovShabat.ClassicalSwapSymmetry
import NLS.ZakharovShabat.ClassicalFreeDiscriminant

/-! # Signed-swap invariance of the actual discriminant

The physical fundamental solution covariance identifies the discriminant after signed potential swap and spectral reflection.
-/

noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

/-- Signed potential swap and spectral reflection preserve the actual trace. -/
theorem classicalDiscriminant_swap (Φ : Curve (ℂ × ℂ)) (z : ℂ) :
    classicalDiscriminant (classicalSwapPotential Φ) (-z) = classicalDiscriminant Φ z := by
  have h₁ := congrArg Prod.fst (classicalSolution_swap Φ z (0,1) ⟨1,by constructor <;> norm_num⟩)
  have h₂ := congrArg Prod.snd (classicalSolution_swap Φ z (1,0) ⟨1,by constructor <;> norm_num⟩)
  simp only [Prod.swap_prod_mk,Prod.fst_swap,Prod.snd_swap] at h₁ h₂
  simp only [classicalDiscriminant,classicalMonodromy,classicalFundamentalMatrix,Matrix.trace_fin_two_of]
  rw [← h₁,← h₂]
  ring

end NLS.ZakharovShabat
