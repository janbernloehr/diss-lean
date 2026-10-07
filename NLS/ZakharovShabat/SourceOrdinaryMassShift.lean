import NLS.ZakharovShabat.SourceOrdinaryFlow

/-! # Exact mass shift between ordinary and renormalized coordinates

The ordinary frequencies differ by four times the physical mass, which
is the total spectral action. The two complex coordinates acquire opposite
scalar phases, with the signs and factor four in Section 22.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceAbelianMomentAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
variable {W : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The ordinary frequency adds four times the actual total spectral action. -/
theorem ordinaryPhaseFrequency_eq_action_shift (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hp2 : p ≤ 2) (φ : realTypeSourceSubmodule p) (n : ℤ) :
    A.ordinaryPhaseFrequency hp2 φ n = A.phaseFrequency φ n +
      4*(∑' k : ℤ, (sourceComplexAction hp hp1 k φ.val).re) := by
  rw [ordinaryPhaseFrequency,phaseFrequency,sourceOrdinaryMass_eq_tsum hp hp1]

/-- The first coordinate has the positive mass rotation relative to renormalized dynamics. -/
theorem ordinaryPhaseTrajectory_massShift_fst (A : SourceAbelianMomentAtlas hp hp1 W s)
    (t : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) (n : ℤ) :
    (A.ordinaryPhaseTrajectory t hp2 φ τ).1 n =
      Complex.exp (((4*τ*sourceOrdinaryMass hp2 φ : ℝ) : ℂ)*I) *
        (A.renormalizedPhaseTrajectory t φ τ).1 n := by
  rw [ordinaryPhaseTrajectory,renormalizedPhaseTrajectory,Birkhoff.phaseFlow_fst,Birkhoff.phaseFlow_fst,
    ← mul_assoc,← Complex.exp_add]
  congr 2
  simp only [ordinaryPhaseFrequency,phaseFrequency]
  push_cast
  ring

/-- The second coordinate has the opposite mass rotation. -/
theorem ordinaryPhaseTrajectory_massShift_snd (A : SourceAbelianMomentAtlas hp hp1 W s)
    (t : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (hp2 : p ≤ 2)
    (φ : realTypeSourceSubmodule p) (τ : ℝ) (n : ℤ) :
    (A.ordinaryPhaseTrajectory t hp2 φ τ).2 n =
      Complex.exp (((-4*τ*sourceOrdinaryMass hp2 φ : ℝ) : ℂ)*I) *
        (A.renormalizedPhaseTrajectory t φ τ).2 n := by
  rw [ordinaryPhaseTrajectory,renormalizedPhaseTrajectory,Birkhoff.phaseFlow_snd,Birkhoff.phaseFlow_snd,
    ← mul_assoc,← Complex.exp_add]
  congr 2
  simp only [ordinaryPhaseFrequency,phaseFrequency]
  push_cast
  ring

end NLS.ZakharovShabat.SourceAbelianMomentAtlas
