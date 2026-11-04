import NLS.ZakharovShabat.SourceActionPhaseFlow
import NLS.ZakharovShabat.SourceComplexBirkhoffExponent

/-! # Exponent compatibility of actual action-invariant source phase lifts -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceActionFrequency
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {hq : q ≠ ⊤} {hq1 : 1 < q}
variable {W₀ B X : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {V₀ C Y : Set (CoeffPair q)} {t : (n : ℤ) → CoeffPair q → DeletedCoeff q n}

/-- Equal original frequencies and compatible actual Birkhoff charts give
compatible full phase trajectories under exponent inclusion. -/
theorem phaseTrajectory_exponent (F : SourceActionFrequency hp hp1) (G : SourceActionFrequency hq hq1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (E : SourceBirkhoffMapComplexData hq hq1 V₀ C Y t) (hpq : p ≤ q)
    (φ : realTypeSourceSubmodule p)
    (hfreq : G.frequency (realTypeSourceExponentInclusion hpq φ) = F.frequency φ) (τ : ℝ) :
    ((Coeff.exponentInclusion hpq).prodMap (Coeff.exponentInclusion hpq)) (F.phaseTrajectory D φ τ) =
      G.phaseTrajectory E (realTypeSourceExponentInclusion hpq φ) τ := by
  unfold phaseTrajectory
  rw [hfreq,← D.complex_map_exponent E hpq φ]
  apply Prod.ext <;> ext n <;> rfl

/-- The actual source image lifts agree under exponent inclusion whenever
both original image conditions hold. No surjectivity is assumed. -/
theorem imageFlow_exponent (F : SourceActionFrequency hp hp1) (G : SourceActionFrequency hq hq1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (E : SourceBirkhoffMapComplexData hq hq1 V₀ C Y t) (hpq : p ≤ q)
    (φ : realTypeSourceSubmodule p)
    (hfreq : G.frequency (realTypeSourceExponentInclusion hpq φ) = F.frequency φ) (τ : ℝ)
    (hφ : (τ,φ) ∈ F.imageDomain D)
    (hψ : (τ,realTypeSourceExponentInclusion hpq φ) ∈ G.imageDomain E) :
    realTypeSourceExponentInclusion hpq (F.imageFlow D φ τ) =
      G.imageFlow E (realTypeSourceExponentInclusion hpq φ) τ := by
  apply E.complex_map_real_injective
  change sourceComplexBirkhoffMap hq hq1 t
    (realTypeSourceExponentInclusion hpq (F.imageFlow D φ τ)).val =
      sourceComplexBirkhoffMap hq hq1 t (G.imageFlow E (realTypeSourceExponentInclusion hpq φ) τ).val
  rw [← D.complex_map_exponent E hpq (F.imageFlow D φ τ),
    F.complex_map_imageFlow D φ τ hφ,G.complex_map_imageFlow E _ τ hψ]
  exact F.phaseTrajectory_exponent G D E hpq φ hfreq τ

end NLS.ZakharovShabat.SourceActionFrequency
