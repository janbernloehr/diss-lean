import NLS.ZakharovShabat.L2MidpointContour
import NLS.ZakharovShabat.L2SourceCharacteristicGradients
import NLS.ZakharovShabat.SourceDiscriminantRegularPoisson
import NLS.ZakharovShabat.SourceMidpointGradientTail

/-! # Actual source midpoint differentials as physical gradient integrals

An isolating circle encloses both indexed periodic endpoints, which may
coincide. The physical contour then represents the actual source derivative
in every included Hilbert direction, retaining finite exponent inclusion.
-/
noncomputable section
open Set Metric Complex MeasureTheory
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourceDiscriminant_exponent_eq_l2 (hp : p ≠ ⊤) (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ : CoeffPair 2) (z : ℂ) :
    canonicalDiscriminant hp (periodOnePotential (CoeffPair.exponentInclusion h2p φ)) z =
      l2Discriminant (sourcePhysicalL2 φ) z := by
  rw [← sourceDiscriminant_exponent (by simp) hp h2p,canonicalDiscriminant_eq_l2_source]

theorem sourceDiscriminantCotangent_exponent_apply_eq_l2 (hp : p ≠ ⊤) (hp1 : 1 < p)
    (h2p : (2 : ℝ≥0∞) ≤ p) (φ h : CoeffPair 2) (z : ℂ) :
    sourceDiscriminantCotangent hp z (CoeffPair.exponentInclusion h2p φ) (CoeffPair.exponentInclusion h2p h) =
      (fderiv ℂ (fun u : IntervalPairL2 => l2Discriminant u z) (sourcePhysicalL2 φ)) (sourcePhysicalL2 h) := by
  have he := congrArg (fun L : CoeffPair 2 →L[ℂ] ℂ => L h)
    (sourceDiscriminantCotangent_exponent (by simp) hp hp1 h2p z φ)
  exact he.symm.trans (sourceDiscriminantCotangent_apply_eq_l2 φ h z)

/-- The actual midpoint gradient is a physical contour, even for a collapsed
gap; geometric isolation supplies the nonzero characteristic denominator. -/
theorem exists_global_source_midpoint_l2_gradient_contour
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ : CoeffPair 2, CoeffPair.exponentInclusion h2p φ ∈ W →
      ∀ (n : ℤ) (c : ℂ) (r : ℝ), 0 < r →
      let ψ := CoeffPair.exponentInclusion h2p φ
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ∈ ball c r →
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ∈ ball c r →
      closedBall c r ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n → ∀ h : CoeffPair 2,
        (fderiv ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
          (periodOnePotential χ) (periodOnePotential_mem χ) n) ψ) (CoeffPair.exponentInclusion h2p h) =
          ∫ s in (0 : ℝ)..1, (l2MidpointGradient (sourcePhysicalL2 φ) c r s).1*
            (physicalBase (periodOnePotential h) s).1+
            (l2MidpointGradient (sourcePhysicalL2 φ) c r s).2*(physicalBase (periodOnePotential h) s).2 := by
  obtain ⟨W,hW,hreal,hformula⟩ := exists_global_source_midpoint_gradient_contour hp hp1
  refine ⟨W,hW,hreal,?_⟩
  intro φ hφ n c r hr
  dsimp only
  intro ha hb hisolate h
  have hne : ∀ z ∈ sphere c r, (l2Discriminant (sourcePhysicalL2 φ) z)^2-4 ≠ 0 := by
    intro z hz
    rw [← sourceDiscriminant_exponent_eq_l2 hp h2p φ z]
    exact canonicalDiscriminant_sq_sub_four_ne_zero_on_isolating_circle hp hp1 _ n c r ha hb hisolate z hz
  rw [← sourcePhysicalL2_gradient_pairing h,l2MidpointGradient_pairing _ _ c r hr.le hne]
  have hf := hformula _ hφ n c r hr ha hb hisolate (CoeffPair.exponentInclusion h2p h)
  change (fderiv ℂ (fun χ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
    (periodOnePotential χ) (periodOnePotential_mem χ) n) (CoeffPair.exponentInclusion h2p φ))
      (CoeffPair.exponentInclusion h2p h) =
      -(2*Real.pi*I : ℂ)⁻¹ * (∮ z in C(c,r),
        canonicalDiscriminant hp (periodOnePotential (CoeffPair.exponentInclusion h2p φ)) z*
        sourceDiscriminantCotangent hp z (CoeffPair.exponentInclusion h2p φ) (CoeffPair.exponentInclusion h2p h)/
          ((canonicalDiscriminant hp (periodOnePotential (CoeffPair.exponentInclusion h2p φ)) z)^2-4)) at hf
  simpa only [sourceDiscriminant_exponent_eq_l2,
    sourceDiscriminantCotangent_exponent_apply_eq_l2 hp hp1] using hf

end NLS.ZakharovShabat
