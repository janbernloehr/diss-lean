import NLS.ZakharovShabat.SourcePrimitivePowerIsospectral
import NLS.ZakharovShabat.SourceFiniteGapPointwiseRenormalizedNLS
import NLS.ZakharovShabat.SourceFiniteGapSobolevHamiltonian

/-! # Conservation of the actual finite-gap physical energy

The trace identity expresses the physical Hamiltonian through the mass,
weighted actions, and cubic primitive-power moments. Equal actions fix
all of these quantities. Both Hamiltonian-oriented flows therefore conserve
the actual physical H¹ energy for every real time.
-/
noncomputable section
open Set Complex NLS.Poisson
namespace NLS.ZakharovShabat

/-- Calibration of the first physical Hamiltonian by the Hilbert mass. -/
theorem sourceFiniteGapNLSHamiltonian_one_eq_ordinaryMass
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 1 =
      (sourceOrdinaryMass le_rfl φ : ℂ) := by
  rw [sourceOrdinaryMass_complex,sourceOrdinaryComplexMass,sourceHilbertMass,
    reflectedHilbertPairing_apply,sourceFiniteGapNLSHamiltonian_one]
  rfl

/-- The actual finite-gap physical energy is constant on action level sets. -/
theorem sourceFiniteGapNLSHamiltonian_three_eq_of_actions
    (φ ψ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (hg : ψ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (h : ∀ n, sourceComplexAction (by simp) (by norm_num) n ψ.val =
      sourceComplexAction (by simp) (by norm_num) n φ.val) :
    sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) ψ hg 3 =
      sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 3 := by
  obtain ⟨W,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas (p := 2) (by simp) (by norm_num)
  have hlevel : ψ ∈ sourceRealActionLevelSet (by simp) (by norm_num) φ := by
    intro n
    rw [← sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n ψ.val ψ.property,
      ← sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) n φ.val φ.property,h n]
  have hm := sourceOrdinaryMass_eq_of_actions (by simp) (by norm_num) le_rfl ψ φ h
  have hi := A.finiteGap_hamiltonian_identity ψ hg
  have hj := A.finiteGap_hamiltonian_identity φ hf
  have hsum : (∑' n : ℤ, A.moment n 3 ψ.val) = ∑' n : ℤ, A.moment n 3 φ.val :=
    tsum_congr (fun n => A.moment_real_eq_of_actions A φ ψ hlevel n 3)
  simp only [h,sourceFiniteGapNLSHamiltonian_one_eq_ordinaryMass,hm,hsum] at hi
  rw [sourceFiniteGapNLSHamiltonian_one_eq_ordinaryMass] at hj
  linear_combination hi - hj

/-- The H¹ Hamiltonian of coefficient-identical finite-gap realizations
has the same conservation law. -/
theorem sourceFiniteGapSobolevHamiltonian_eq_of_actions
    (φ ψ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (hg : ψ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (h : ∀ n, sourceComplexAction (by simp) (by norm_num) n ψ.val =
      sourceComplexAction (by simp) (by norm_num) n φ.val) :
    periodOneSobolevHamiltonian (sourceFiniteGapSobolevPair (by simp) (by norm_num) ψ hg) =
      periodOneSobolevHamiltonian (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf) := by
  rw [periodOneSobolevHamiltonian_sourceFiniteGapSobolevPair,
    periodOneSobolevHamiltonian_sourceFiniteGapSobolevPair]
  exact sourceFiniteGapNLSHamiltonian_three_eq_of_actions φ ψ hf hg h

namespace SourceAbelianMomentAtlas
variable {W V B X : Set (CoeffPair 2)}
variable {s t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Ordinary physical NLS conserves the finite-gap H¹ energy for all time. -/
theorem hamiltonianOrdinarySourceFlow_energy
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) :
    periodOneSobolevHamiltonian (sourceFiniteGapSobolevPair (by simp) (by norm_num)
      (A.hamiltonianOrdinarySourceFlow D le_rfl φ time)
      (A.hamiltonianOrdinarySourceFlow_finiteGap D le_rfl φ hf time)) =
        periodOneSobolevHamiltonian (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf) :=
  sourceFiniteGapSobolevHamiltonian_eq_of_actions φ _ hf _
    (A.hamiltonianOrdinarySourceFlow_action D le_rfl φ time)

/-- The mass rotation also preserves the actual finite-gap physical energy. -/
theorem hamiltonianRenormalizedSourceFlow_energy
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (time : ℝ) :
    periodOneSobolevHamiltonian (sourceFiniteGapSobolevPair (by simp) (by norm_num)
      (A.hamiltonianRenormalizedSourceFlow D le_rfl φ time)
      (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf time)) =
        periodOneSobolevHamiltonian (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf) :=
  sourceFiniteGapSobolevHamiltonian_eq_of_actions φ _ hf _
    (A.hamiltonianRenormalizedSourceFlow_action D le_rfl φ time)

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
