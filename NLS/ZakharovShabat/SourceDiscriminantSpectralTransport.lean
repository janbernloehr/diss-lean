import NLS.ZakharovShabat.SourceComponentSwapRoots
import NLS.ZakharovShabat.PeriodicSpectralDataUniqueness

/-! # Transport of intrinsic spectral data from an actual discriminant identity

The original algebraic multiplicities, globally signed endpoint labels and
normalized canonical root are determined by equality of the entire physical
source discriminants. No candidate endpoint relabeling or root sign is assumed.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourcePeriodicSpectrum_eq_of_discriminant_eq (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p)
    (he : ∀ z, canonicalDiscriminant hp (periodOnePotential φ) z =
      canonicalDiscriminant hp (periodOnePotential ψ) z) :
    periodicSpectrum hp (periodOnePotential φ) = periodicSpectrum hp (periodOnePotential ψ) := by
  ext z
  rw [← canonicalDiscriminant_sq_eq_four_iff_finite hp hp1 _ (periodOnePotential_mem _) z,
    he z,canonicalDiscriminant_sq_eq_four_iff_finite hp hp1 _ (periodOnePotential_mem _) z]

theorem sourcePeriodicMultiplicity_eq_of_discriminant_eq (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p)
    (he : ∀ z, canonicalDiscriminant hp (periodOnePotential φ) z =
      canonicalDiscriminant hp (periodOnePotential ψ) z) (z : ℂ) :
    periodicAlgebraicMultiplicity hp (periodOnePotential φ) z =
      periodicAlgebraicMultiplicity hp (periodOnePotential ψ) z := by
  have hf : (fun w : ℂ => (canonicalDiscriminant hp (periodOnePotential φ) w)^2-4) =
      (fun w : ℂ => (canonicalDiscriminant hp (periodOnePotential ψ) w)^2-4) := by
    funext w
    rw [he w]
  have ho := congrArg (fun f : ℂ → ℂ => analyticOrderAt f z) hf
  rw [analyticOrderAt_canonicalDiscriminant_sq_sub_four hp hp1 _ (periodOnePotential_mem _) z,
    analyticOrderAt_canonicalDiscriminant_sq_sub_four hp hp1 _ (periodOnePotential_mem _) z] at ho
  exact_mod_cast ho

theorem sourceCanonicalPeriodicEndpoints_eq_of_discriminant_eq (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p)
    (he : ∀ z, canonicalDiscriminant hp (periodOnePotential φ) z =
      canonicalDiscriminant hp (periodOnePotential ψ) z) :
    canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) =
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) ∧
    canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem _) =
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem _) :=
  canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1 _ _
    (periodOnePotential_mem _) (periodOnePotential_mem _)
    (sourcePeriodicSpectrum_eq_of_discriminant_eq hp hp1 φ ψ he)
    (sourcePeriodicMultiplicity_eq_of_discriminant_eq hp hp1 φ ψ he)

theorem sourceStandardRoot_eq_of_discriminant_eq (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p)
    (he : ∀ z, canonicalDiscriminant hp (periodOnePotential φ) z =
      canonicalDiscriminant hp (periodOnePotential ψ) z) (n : ℤ) (z : ℂ) :
    sourceStandardRoot hp hp1 φ n z = sourceStandardRoot hp hp1 ψ n z := by
  obtain ⟨hl,hr⟩ := sourceCanonicalPeriodicEndpoints_eq_of_discriminant_eq hp hp1 φ ψ he
  unfold sourceStandardRoot canonicalPeriodicMidpoint canonicalPeriodicGap
  rw [hl,hr]

theorem sourceCanonicalRoot_eq_of_discriminant_eq (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p)
    (he : ∀ z, canonicalDiscriminant hp (periodOnePotential φ) z =
      canonicalDiscriminant hp (periodOnePotential ψ) z) (z : ℂ) :
    sourceCanonicalRoot hp hp1 φ z = sourceCanonicalRoot hp hp1 ψ z := by
  simp only [sourceCanonicalRoot,sourceStandardRootPairedProduct,
    sourceStandardRootPairedFactor,sourceStandardRoot_eq_of_discriminant_eq hp hp1 φ ψ he]

end NLS.ZakharovShabat
