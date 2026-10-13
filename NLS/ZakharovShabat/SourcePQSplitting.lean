import NLS.ZakharovShabat.SourceWeightedPencil
import NLS.ZakharovShabat.ResonantCoordinates

/-!
# The original source eigenvalue equation and the P/Q splitting

The direct decomposition is unique and uses the actual weighted derivative
domain. Its two equations are equivalent to the original source spectral
pencil, without any small-potential or distant-frequency hypothesis.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The free pencil commutes with the resonant projection on its actual derivative domain. -/
theorem weightedFreePencil_resonantProjection (w : Weight) (n : ℤ) (z : ℂ) (f : WeightedDomain w p) :
    weightedFreePencil w z (resonantProjection w.oneDerivative n f) =
      resonantProjection w n (weightedFreePencil w z f) := by
  apply weightedPair_ext <;> intro k <;> simp

/-- Every weighted vector has unique resonant coordinates and a complementary remainder. -/
theorem exists_unique_sourcePQDecomposition (w : Weight) (n : ℤ) (f : WeightedCoeffPair w p) :
    ∃! cv : (Fin 2 → ℂ) × WeightedCoeffPair w p,
      complementaryProjection w n cv.2 = cv.2 ∧ resonantSynthesis w n cv.1 + cv.2 = f := by
  refine ⟨(resonantCoordinates w n f,complementaryProjection w n f),?_,?_⟩
  · exact ⟨complementaryProjection_idempotent w n f,
      by rw [resonantSynthesis_coordinates]; exact resonant_add_complementary w n f⟩
  · rintro ⟨c,v⟩ ⟨hv,he⟩
    have hq := congrArg (complementaryProjection w n) he
    simp only [map_add,complementary_resonantSynthesis,zero_add,hv] at hq
    have hc := congrArg (resonantCoordinates w n) he
    rw [map_add,resonantCoordinates_synthesis,← hv,resonantCoordinates_complementary,add_zero] at hc
    exact Prod.ext hc hq

/-- Equality is detected by the two complementary projections. -/
theorem weighted_eq_iff_PQ (w : Weight) (n : ℤ) (f g : WeightedCoeffPair w p) :
    f = g ↔ resonantProjection w n f = resonantProjection w n g ∧
      complementaryProjection w n f = complementaryProjection w n g := by
  constructor
  · rintro rfl; exact ⟨rfl,rfl⟩
  · rintro ⟨hp,hq⟩
    calc
      f = resonantProjection w n f + complementaryProjection w n f := (resonant_add_complementary w n f).symm
      _ = resonantProjection w n g + complementaryProjection w n g := by rw [hp,hq]
      _ = g := resonant_add_complementary w n g

/-- The original pencil vanishes exactly when its actual resonant and complementary equations hold. -/
theorem sourceWeightedPencil_zero_iff_PQ (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (f : WeightedDomain w.toWeight p) :
    sourceSpectralPencil hp (sourceWeightedPeriodTwoInput w φ) z (sourceWeightedDomainInput w f) = 0 ↔
      weightedFreePencil w.toWeight z (resonantProjection w.toWeight.oneDerivative n f) =
        resonantProjection w.toWeight n (weightedDomainPotential hp w φ f) ∧
      weightedFreePencil w.toWeight z (complementaryProjection w.toWeight.oneDerivative n f) =
        complementaryProjection w.toWeight n (weightedDomainPotential hp w φ f) := by
  rw [sourceWeightedPencil_zero_iff,weightedFreePencil_resonantProjection,pencil_complementaryProjection]
  exact weighted_eq_iff_PQ w.toWeight n _ _

/-- The P/Q equations for a specified resonant part and complementary part are equivalent to the original equation. -/
theorem sourceWeightedPencil_add_zero_iff_PQ (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (u v : WeightedDomain w.toWeight p)
    (hu : resonantProjection w.toWeight.oneDerivative n u = u)
    (hv : complementaryProjection w.toWeight.oneDerivative n v = v) :
    sourceSpectralPencil hp (sourceWeightedPeriodTwoInput w φ) z (sourceWeightedDomainInput w (u+v)) = 0 ↔
      weightedFreePencil w.toWeight z u = resonantProjection w.toWeight n (weightedDomainPotential hp w φ (u+v)) ∧
      weightedFreePencil w.toWeight z v = complementaryProjection w.toWeight n (weightedDomainPotential hp w φ (u+v)) := by
  have hpu : complementaryProjection w.toWeight.oneDerivative n u = 0 := by
    rw [← hu,complementary_resonant_zero]
  have hqv : resonantProjection w.toWeight.oneDerivative n v = 0 := by
    rw [← hv,resonant_complementary_zero]
  simpa only [map_add,hu,hv,hpu,hqv,add_zero,zero_add] using
    sourceWeightedPencil_zero_iff_PQ hp w φ n z (u+v)

/-- The actual complementary inverse solves the original free source equation with right-hand side Q_n f. -/
theorem sourceComplementaryFreeInverse_equation (hp : p ≠ ⊤) (w : SpectralWeight)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (f : WeightedCoeffPair w.toWeight p) :
    sourceSpectralPencil hp 0 z
      (sourceWeightedDomainInput w (complementaryFreeDomainInverse w.toWeight n z hz f)) =
        sourceWeightedPeriodTwoInput w (complementaryProjection w.toWeight n f) := by
  rw [sourceWeightedFreePencil_eq,pencil_complementaryFreeDomainInverse]

/-- The complementary solution of the original free source equation is unique in the weighted domain. -/
theorem sourceComplementaryFreeInverse_unique (hp : p ≠ ⊤) (w : SpectralWeight)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (f : WeightedCoeffPair w.toWeight p)
    (v : WeightedDomain w.toWeight p)
    (hv : complementaryProjection w.toWeight.oneDerivative n v = v)
    (he : sourceSpectralPencil hp 0 z (sourceWeightedDomainInput w v) =
      sourceWeightedPeriodTwoInput w (complementaryProjection w.toWeight n f)) :
    v = complementaryFreeDomainInverse w.toWeight n z hz f := by
  rw [sourceWeightedFreePencil_eq] at he
  exact complementaryFreeDomainInverse_unique w.toWeight n z hz f v hv
    ((sourceWeightedPeriodTwoInput_injective w) he)

/-- The complementary domain inverse kills both resonant modes, including at the free lattice center. -/
theorem sourceComplementaryFreeInverse_resonant (w : SpectralWeight) (n : ℤ)
    (z : ℂ) (hz : z ∈ resonantStrip n) (c : Fin 2 → ℂ) :
    complementaryFreeDomainInverse w.toWeight n z hz (resonantSynthesis (p := p) w.toWeight n c) = 0 := by
  apply weightedPair_ext <;> intro k
  · by_cases hk : k = -n <;> simp [hk]
  · by_cases hk : k = n <;> simp [hk]

end NLS.ZakharovShabat
