import NLS.ZakharovShabat.FiniteParityCompatibility

/-!
# Spectral characterization and uniqueness of the finite-p discriminant

Both parity levels and the full characteristic equation recover the original
spectrum. Agreement with the Hilbert discriminant on the dense absolutely
summable potentials determines the extension uniquely, even among continuous
functions at each fixed spectral parameter.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The two discriminant levels recover the original parity spectra at every finite p>1. -/
theorem canonicalDiscriminant_parity_levels_finite (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    (canonicalDiscriminant hp φ z = 2 ↔ 0 < parityAlgebraicMultiplicity hp φ 0 z) ∧
    (canonicalDiscriminant hp φ z = -2 ↔ 0 < parityAlgebraicMultiplicity hp φ 1 z) := by
  have he := ((canonicalParityProduct_spec hp hp1 φ hφ 0 (Or.inl rfl)).2 z).2
  have ho := ((canonicalParityProduct_spec hp hp1 φ hφ 1 (Or.inr rfl)).2 z).2
  rw [canonicalEven_eq_discriminant_sub_two, sub_eq_zero] at he
  rw [canonicalOdd_eq_discriminant_add_two_finite hp hp1 φ hφ, add_eq_zero_iff_eq_neg] at ho
  exact ⟨he, ho⟩

/-- The characteristic equation gives precisely the original full periodic spectrum. -/
theorem canonicalDiscriminant_sq_eq_four_iff_finite (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    (canonicalDiscriminant hp φ z)^2 = 4 ↔ z ∈ periodicSpectrum hp φ := by
  have h := canonicalPeriodicProduct_eq_zero_iff hp hp1 φ z
  rw [canonicalPeriodic_eq_discriminant_sq_sub_four_finite hp hp1 φ hφ, sub_eq_zero] at h
  exact h

/-- The full characteristic vanishing order is the original algebraic multiplicity. -/
theorem analyticOrderAt_canonicalDiscriminant_sq_sub_four (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0) (z : ℂ) :
    analyticOrderAt (fun w => (canonicalDiscriminant hp φ w)^2-4) z =
      (periodicAlgebraicMultiplicity hp φ z : ℕ∞) := by
  have he : (fun w => (canonicalDiscriminant hp φ w)^2-4) = canonicalPeriodicProduct hp φ :=
    funext (fun w => (canonicalPeriodic_eq_discriminant_sq_sub_four_finite hp hp1 φ hφ w).symm)
  rw [he]
  exact analyticOrderAt_canonicalPeriodicProduct hp hp1 φ z

/-- Free normalization is the same at every finite ambient exponent. -/
theorem canonicalDiscriminant_zero_finite (hp : p ≠ ⊤) (z : ℂ) :
    canonicalDiscriminant hp (0 : PairSpace p) z = freeDiscriminant z := by
  rcases le_total p 2 with hp2 | h2p
  · rw [canonicalDiscriminant_exponent hp (by simp) hp2, map_zero, canonicalDiscriminant_zero]
  · have h := canonicalDiscriminant_exponent (by simp) hp h2p 0 z
    simpa only [map_zero, canonicalDiscriminant_zero] using h.symm

/-- Uniqueness of the continuous extension from absolutely summable Hilbert potentials. -/
theorem canonicalDiscriminant_unique_continuous (hp : p ≠ ⊤) (hp1 : 1 < p) (z : ℂ)
    (F : pairParitySubspace (p := p) 0 → ℂ) (hF : Continuous F)
    (hagree : ∀ ψ : PairSpace 1, ∀ hψ : ψ ∈ pairParitySubspace 0,
      F ⟨pairExponentInclusion (show (1 : ENNReal) ≤ p from Fact.out) ψ,
          (pairExponentInclusion_mem_parity_iff _ ψ 0).mpr hψ⟩ =
        canonicalDiscriminant (by simp) (pairExponentInclusion (by norm_num : (1 : ENNReal) ≤ 2) ψ) z) :
    F = fun φ => canonicalDiscriminant hp φ.val z := by
  have hc : Continuous (fun φ : pairParitySubspace (p := p) 0 => canonicalDiscriminant hp φ.val z) :=
    (continuous_canonicalParityProduct_potential hp hp1 0 (Or.inl rfl) z).add continuous_const
  apply Continuous.ext_on (dense_pairExponentInclusion_parity hp (show (1 : ENNReal) ≤ p from Fact.out) 0) hF hc
  rintro φ ⟨ψ, hψ⟩
  have hpar : ψ ∈ pairParitySubspace 0 :=
    (pairExponentInclusion_mem_parity_iff _ ψ 0).mp (hψ ▸ φ.property)
  have he : (⟨pairExponentInclusion (show (1 : ENNReal) ≤ p from Fact.out) ψ,
      (pairExponentInclusion_mem_parity_iff _ ψ 0).mpr hpar⟩ : pairParitySubspace (p := p) 0) = φ :=
    Subtype.ext hψ
  have h := hagree ψ hpar
  rw [he] at h
  dsimp only
  rw [h, ← canonicalDiscriminant_exponent (by simp) (by simp) (by norm_num : (1 : ENNReal) ≤ 2),
    ← hψ, ← canonicalDiscriminant_exponent (by simp) hp]

end NLS.ZakharovShabat
