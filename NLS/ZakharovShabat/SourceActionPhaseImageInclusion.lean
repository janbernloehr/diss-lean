import NLS.ZakharovShabat.SourceActionPhaseExponent

/-! # Admissibility of actual phase lifts under exponent inclusion

An admissible source trajectory itself supplies a point in the larger
Birkhoff image. No global surjectivity of that larger image is required.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceActionFrequency
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {hq : q ≠ ⊤} {hq1 : 1 < q}
variable {W₀ B X : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
variable {V₀ C Y : Set (CoeffPair q)} {t : (n : ℤ) → CoeffPair q → DeletedCoeff q n}

theorem mem_imageDomain_exponent (F : SourceActionFrequency hp hp1) (G : SourceActionFrequency hq hq1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (E : SourceBirkhoffMapComplexData hq hq1 V₀ C Y t) (hpq : p ≤ q)
    (φ : realTypeSourceSubmodule p)
    (hfreq : G.frequency (realTypeSourceExponentInclusion hpq φ) = F.frequency φ) (τ : ℝ)
    (hφ : (τ,φ) ∈ F.imageDomain D) :
    (τ,realTypeSourceExponentInclusion hpq φ) ∈ G.imageDomain E := by
  let ψ := F.imageFlow D φ τ
  have hc : sourceComplexBirkhoffMap hq hq1 t (realTypeSourceExponentInclusion hpq ψ).val =
      G.phaseTrajectory E (realTypeSourceExponentInclusion hpq φ) τ := by
    rw [← D.complex_map_exponent E hpq ψ,F.complex_map_imageFlow D φ τ hφ]
    exact F.phaseTrajectory_exponent G D E hpq φ hfreq τ
  refine ⟨realTypeSourceExponentInclusion hpq ψ,?_⟩
  have henc := (E.encode_real_map (realTypeSourceExponentInclusion hpq ψ)).trans hc
  exact (Birkhoff.decodeReal_encodeReal _).symm.trans (congrArg Birkhoff.decodeReal henc)

theorem imageFlow_exponent_of_mem (F : SourceActionFrequency hp hp1) (G : SourceActionFrequency hq hq1)
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B X s)
    (E : SourceBirkhoffMapComplexData hq hq1 V₀ C Y t) (hpq : p ≤ q)
    (φ : realTypeSourceSubmodule p)
    (hfreq : G.frequency (realTypeSourceExponentInclusion hpq φ) = F.frequency φ) (τ : ℝ)
    (hφ : (τ,φ) ∈ F.imageDomain D) :
    realTypeSourceExponentInclusion hpq (F.imageFlow D φ τ) =
      G.imageFlow E (realTypeSourceExponentInclusion hpq φ) τ :=
  F.imageFlow_exponent G D E hpq φ hfreq τ hφ (F.mem_imageDomain_exponent G D E hpq φ hfreq τ hφ)

end NLS.ZakharovShabat.SourceActionFrequency
