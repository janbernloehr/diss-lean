import NLS.ZakharovShabat.SourceSection19Primitive
import NLS.ZakharovShabat.SourceFullAbelianCubeAsymptotics

/-!
# The original Section 19 Laurent expansions on the common neighborhood

The coefficients are the physical Hamiltonians of the constructed smooth
representative of each real finite-gap source. All complex directions and
all normalization indices share one exterior radius and remainder bound.
-/
noncomputable section
open Set Metric Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
  {W U : Set (CoeffPair p)}
namespace SourceSection19Data
variable (D : SourceSection19Data hp hp1 W U)
include D

/-- Lemma 19.2 for the same primitive used in the original endpoint integrals. -/
theorem laurent (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ R : ℝ, 0 < R ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,φ.val))
        {z : ℂ | R < ‖z‖}) ∧
      ∀ (n : ℤ) (z : ℂ), R < ‖z‖ →
        HasSum (fun k : ℕ => Complex.I*sourceFiniteGapNLSHamiltonian hp hp1 φ hf (k+1)/(2*z)^(k+1))
          (sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)+Complex.I*z-Complex.I*(Real.pi : ℂ)*n) := by
  obtain ⟨C,hC⟩ := D.cauchyFamily φ.val (D.real_subset φ.property)
  exact exists_sourceFullAbelian_finiteGap_hamiltonian_laurent C φ hC hf

/-- Corollary 19.3 with one quantitative bound for all normalization indices. -/
theorem cube_asymptotic (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ R : ℝ, 0 < R ∧ ∃ K : ℝ, 0 < K ∧
      (∀ n : ℤ, AnalyticOnNhd ℂ
        (fun z => (sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)-Complex.I*(Real.pi : ℂ)*n)^3)
        {z : ℂ | R < ‖z‖}) ∧
      ∀ (n : ℤ) (z : ℂ), R < ‖z‖ →
        ‖(sourceFullAbelianPrimitive hp hp1 W n (z,φ.val)-Complex.I*(Real.pi : ℂ)*n)^3-
          phaseCubeLaurentPart (sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1)
            (sourceFiniteGapNLSHamiltonian hp hp1 φ hf 2)
            (sourceFiniteGapNLSHamiltonian hp hp1 φ hf 3) z‖ ≤ K/‖z‖^2 := by
  obtain ⟨C,hC⟩ := D.cauchyFamily φ.val (D.real_subset φ.property)
  exact exists_sourceFullAbelian_finiteGap_cube_asymptotics C φ hC hf

/-- The printed cubic formula, with its literal Hamiltonians and big-O remainder. -/
theorem cube_isBigO (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    (fun z : ℂ => (sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val))^3-
      (Complex.I*z^3-(3*Complex.I/2)*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1*z-
        (3*Complex.I/4)*sourceFiniteGapNLSHamiltonian hp hp1 φ hf 2-
        (3*Complex.I/8)*(sourceFiniteGapNLSHamiltonian hp hp1 φ hf 3-
          2*(sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1)^2)/z))
      =O[Bornology.cobounded ℂ] (fun z : ℂ => z⁻¹^2) := by
  obtain ⟨C,hC⟩ := D.cauchyFamily φ.val (D.real_subset φ.property)
  exact sourceFullAbelian_finiteGap_cube_isBigO C φ hC hf

end SourceSection19Data
end NLS.ZakharovShabat
