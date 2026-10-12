import NLS.ZakharovShabat.L2CharacteristicGradients
import NLS.ZakharovShabat.ClassicalCharacteristicGradientRemainders

/-! # Exact agreement of physical L2 and classical gradients on the unit interval -/

noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

theorem l2EndpointGradient_of_continuous (Φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) (ℓ : (ℂ × ℂ) →L[ℂ] ℂ)
    (s : Icc (0 : ℝ) 1) :
    l2EndpointGradient (continuousPotentialL2Class Φ) z v ℓ ⟨1,by norm_num⟩ s =
      classicalEndpointGradient Φ z v ℓ s := by
  simp only [l2EndpointGradient,classicalEndpointGradient,l2SolutionCurve_of_continuous,
    extend_coe,classicalSolutionCurve_apply]

theorem l2DiscriminantGradient_of_continuous (Φ : Curve (ℂ × ℂ)) (z : ℂ) (s : Icc (0 : ℝ) 1) :
    l2DiscriminantGradient (continuousPotentialL2Class Φ) z s = classicalDiscriminantGradient Φ z s := by
  simp only [l2DiscriminantGradient,l2EndpointGradient_of_continuous]
  apply Prod.ext <;>
    simp only [classicalEndpointGradient,classicalDiscriminantGradient,classicalMonodromy,
      classicalFundamentalMatrix,Prod.fst_add,Prod.snd_add,
      ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd'] <;> dsimp <;> ring

theorem l2AntiDiscriminantGradient_of_continuous (Φ : Curve (ℂ × ℂ)) (z : ℂ) (s : Icc (0 : ℝ) 1) :
    l2AntiDiscriminantGradient (continuousPotentialL2Class Φ) z s = classicalAntiDiscriminantGradient Φ z s := by
  simp only [l2AntiDiscriminantGradient,classicalAntiDiscriminantGradient,l2EndpointGradient_of_continuous]

theorem l2SeparatedGradient_of_continuous (b : BoundaryCondition) (Φ : Curve (ℂ × ℂ)) (z : ℂ) (s : Icc (0 : ℝ) 1) :
    l2SeparatedGradient b (continuousPotentialL2Class Φ) z s = classicalSeparatedGradient b Φ z s := by
  simp only [l2SeparatedGradient,classicalSeparatedGradient,l2EndpointGradient_of_continuous]

/-- Subtract the actual free physical gradient at the reference frequency. -/
def l2AntiDiscriminantGradientRemainder (u : IntervalPairL2) (z w : ℂ) (s : ℝ) : ℂ × ℂ :=
  l2AntiDiscriminantGradient u z s-l2AntiDiscriminantGradient 0 w s

theorem l2AntiDiscriminantGradient_free (w : ℂ) (s : Icc (0 : ℝ) 1) :
    l2AntiDiscriminantGradient 0 w s = classicalFreeAntiDiscriminantGradient w s := by
  rw [← continuousPotentialL2Class_zero,l2AntiDiscriminantGradient_of_continuous]
  simp only [classicalAntiDiscriminantGradient,classicalFreeAntiDiscriminantGradient,
    classicalEndpointGradient_free]

theorem l2AntiDiscriminantGradientRemainder_of_continuous
    (Φ : Curve (ℂ × ℂ)) (z w : ℂ) (s : Icc (0 : ℝ) 1) :
    l2AntiDiscriminantGradientRemainder (continuousPotentialL2Class Φ) z w s =
      classicalAntiDiscriminantGradientRemainder Φ z w s := by
  rw [l2AntiDiscriminantGradientRemainder,l2AntiDiscriminantGradient_of_continuous,
    l2AntiDiscriminantGradient_free]
  rfl

/-- The corrected reference uses the actual signed waves at every integer index. -/
theorem l2AntiDiscriminantGradientRemainder_lattice (u : IntervalPairL2) (z : ℂ)
    (n : ℤ) (s : Icc (0 : ℝ) 1) :
    l2AntiDiscriminantGradientRemainder u z ((Real.pi : ℂ)*n) s =
      l2AntiDiscriminantGradient u z s-
        (I*cos ((Real.pi : ℂ)*n)*NLS.Fourier.wave (2*n) s,
         -I*cos ((Real.pi : ℂ)*n)*NLS.Fourier.wave (-(2*n)) s) := by
  rw [l2AntiDiscriminantGradientRemainder,l2AntiDiscriminantGradient_free,
    classicalFreeAntiDiscriminantGradient_lattice]

end NLS.ZakharovShabat
