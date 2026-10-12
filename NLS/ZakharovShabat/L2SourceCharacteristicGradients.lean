import NLS.ZakharovShabat.L2CharacteristicGradients
import NLS.ZakharovShabat.L2DiscriminantCotangent

/-! # Original Hilbert source cotangents as physical gradient integrals -/
noncomputable section
open Set Complex MeasureTheory
namespace NLS.ZakharovShabat

/-- Change only the L2 representative, retaining the original Fourier normalization. -/
theorem sourcePhysicalL2_gradient_pairing (h : CoeffPair 2) (g : ℝ → ℂ × ℂ) :
    (∫ s in (0 : ℝ)..1, (g s).1*(sourcePhysicalL2 h).ofLp.1 s+
      (g s).2*(sourcePhysicalL2 h).ofLp.2 s) =
    ∫ s in (0 : ℝ)..1, (g s).1*(physicalBase (periodOnePotential h) s).1+
      (g s).2*(physicalBase (periodOnePotential h) s).2 := by
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  filter_upwards [sourcePhysicalL2_representative h] with s hs
  have h₁ := congrArg Prod.fst hs
  have h₂ := congrArg Prod.snd hs
  change (sourcePhysicalL2 h).ofLp.1 s = (physicalBase (periodOnePotential h) s).1 at h₁
  change (sourcePhysicalL2 h).ofLp.2 s = (physicalBase (periodOnePotential h) s).2 at h₂
  rw [h₁,h₂]

/-- The full source discriminant cotangent is its actual unconjugated physical integral. -/
theorem sourceDiscriminantCotangent_eq_physical_gradient_integral (φ h : CoeffPair 2) (z : ℂ) :
    sourceDiscriminantCotangent (by simp) z φ h =
      ∫ s in (0 : ℝ)..1, (l2DiscriminantGradient (sourcePhysicalL2 φ) z s).1*
        (physicalBase (periodOnePotential h) s).1+
        (l2DiscriminantGradient (sourcePhysicalL2 φ) z s).2*(physicalBase (periodOnePotential h) s).2 := by
  rw [sourceDiscriminantCotangent_apply_eq_l2,fderiv_l2Discriminant_eq_gradient_integral]
  exact sourcePhysicalL2_gradient_pairing h _

/-- The original anti-discriminant has the same physical formula in every Hilbert direction. -/
theorem sourceAntiDiscriminantCotangent_eq_physical_gradient_integral (φ h : CoeffPair 2) (z : ℂ) :
    sourceAntiDiscriminantCotangent (by simp) (by norm_num) z φ h =
      ∫ s in (0 : ℝ)..1, (l2AntiDiscriminantGradient (sourcePhysicalL2 φ) z s).1*
        (physicalBase (periodOnePotential h) s).1+
        (l2AntiDiscriminantGradient (sourcePhysicalL2 φ) z s).2*(physicalBase (periodOnePotential h) s).2 := by
  rw [sourceAntiDiscriminantCotangent_apply_eq_l2,fderiv_l2AntiDiscriminant_eq_gradient_integral]
  exact sourcePhysicalL2_gradient_pairing h _

/-- Both boundary cotangents use the original signed physical gradient and source realization. -/
theorem sourceBoundaryCharacteristicCotangent_eq_physical_gradient_integral
    (b : BoundaryCondition) (φ h : CoeffPair 2) (z : ℂ) :
    sourceBoundaryCharacteristicCotangent (by simp) (by norm_num) b z φ h =
      ∫ s in (0 : ℝ)..1, (l2SeparatedGradient b (sourcePhysicalL2 φ) z s).1*
        (physicalBase (periodOnePotential h) s).1+
        (l2SeparatedGradient b (sourcePhysicalL2 φ) z s).2*(physicalBase (periodOnePotential h) s).2 := by
  rw [sourceBoundaryCharacteristicCotangent_apply_eq_l2,fderiv_l2SeparatedCharacteristic_eq_gradient_integral]
  exact sourcePhysicalL2_gradient_pairing h _

end NLS.ZakharovShabat
