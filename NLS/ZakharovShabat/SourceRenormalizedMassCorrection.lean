import NLS.ZakharovShabat.SourceMassActionDifferential
import NLS.ZakharovShabat.SourceFiniteGapPhysicalNLSODE
import NLS.ZakharovShabat.SourceFiniteGapRenormalizedSobolevTime

/-! # The physical mass correction in the renormalized source velocity

The finite sum of action fields with constant frequency one is the mass
Hamiltonian field. Subtracting four times the physical mass from every
ordinary frequency therefore adds four times the mass times sourcePhase
to the physical NLS velocity, with no unproved gauge-equivariance premise.
-/
noncomputable section
open Set Complex NLS.Poisson
namespace NLS.ZakharovShabat

/-- The finite action trace identifies the mass Hamiltonian direction. -/
theorem sourceFiniteActionHamiltonianVector_one
    (φ : realTypeSourceSubmodule 2) (S : Finset ℤ)
    (hS : ∀ n ∉ S, fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) φ.val = 0) :
    sourceFiniteActionHamiltonianVector (by simp) (by norm_num) le_rfl (fun _ => 1) S φ.val =
      -sourcePhase φ.val := by
  have he : fderiv ℂ sourceHilbertMass φ.val =
      ∑ n ∈ S, fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) φ.val := by
    apply ContinuousLinearMap.ext
    intro h
    simpa only [sum_apply] using sourceHilbertMass_fderiv_eq_finite_sum φ S hS h
  rw [← sourceHamiltonianVector_sourceHilbertMass_eq_neg_sourcePhase,sourceHamiltonianVector,he]
  simp only [sourceFiniteActionHamiltonianVector,ofReal_one,one_smul,map_sum,sourceHamiltonianVector]

namespace SourceAbelianMomentAtlas
variable {W P V B X : Set (CoeffPair 2)}
variable {s t : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- At each finite cutoff the renormalized field is the ordinary field
plus the exact physical mass rotation. -/
theorem finiteActionHamiltonianVector_renormalized_eq
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (φ : realTypeSourceSubmodule 2) (S : Finset ℤ)
    (hS : ∀ n ∉ S, fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) φ.val = 0) :
    sourceFiniteActionHamiltonianVector (by simp) (by norm_num) le_rfl (A.phaseFrequency φ) S φ.val =
      sourceFiniteActionHamiltonianVector (by simp) (by norm_num) le_rfl
        (A.ordinaryPhaseFrequency le_rfl φ) S φ.val +
      (4*sourceOrdinaryMass le_rfl φ : ℂ) • sourcePhase φ.val := by
  have hf : A.phaseFrequency φ = fun n => A.ordinaryPhaseFrequency le_rfl φ n -
      4*sourceOrdinaryMass le_rfl φ := by
    funext n
    simp only [phaseFrequency,ordinaryPhaseFrequency,add_sub_cancel_right]
  rw [hf]
  have he : sourceFiniteActionHamiltonianVector (by simp) (by norm_num) le_rfl
      (fun n => A.ordinaryPhaseFrequency le_rfl φ n - 4*sourceOrdinaryMass le_rfl φ) S φ.val =
      sourceFiniteActionHamiltonianVector (by simp) (by norm_num) le_rfl
        (A.ordinaryPhaseFrequency le_rfl φ) S φ.val -
      (4*sourceOrdinaryMass le_rfl φ : ℂ) •
        sourceFiniteActionHamiltonianVector (by simp) (by norm_num) le_rfl (fun _ => 1) S φ.val := by
    simp only [sourceFiniteActionHamiltonianVector,ofReal_sub,ofReal_mul,ofReal_ofNat,
      sub_smul,Finset.sum_sub_distrib,ofReal_one,one_smul,Finset.smul_sum]
  rw [he,sourceFiniteActionHamiltonianVector_one φ S hS,smul_neg,sub_neg_eq_add]

/-- The ordinary finite action field is the physical NLS field at every
finite-gap source; derivative uniqueness fixes its sign and normalization. -/
theorem finiteActionHamiltonianVector_eq_physicalNLS
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (S : Finset ℤ)
    (hz : ∀ n ∉ S, (sourceComplexBirkhoffMap (by simp) (by norm_num) t φ.val).1 n = 0 ∧
      (sourceComplexBirkhoffMap (by simp) (by norm_num) t φ.val).2 n = 0) :
    sourceFiniteActionHamiltonianVector (by simp) (by norm_num) le_rfl
      (A.ordinaryPhaseFrequency le_rfl φ) S φ.val = sourceFiniteGapPhysicalNLSCoefficients φ hf := by
  have he := (A.hasDerivAt_hamiltonianOrdinarySourceFlow_finiteAction D le_rfl le_rfl φ S hz 0).unique
    (A.hasDerivAt_hamiltonianOrdinarySourceFlow_physicalNLS hs D φ hf 0)
  simpa only [A.hamiltonianOrdinarySourceFlow_zero] using he

/-- The full Hilbert derivative of the renormalized trajectory is the
actual NLS field plus the mass rotation, with conserved initial mass. -/
theorem hasDerivAt_hamiltonianRenormalizedSourceFlow_physicalNLS
    (A : SourceAbelianMomentAtlas (by simp) (by norm_num) W s)
    (hs : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P s)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) V B X t)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (time : ℝ) :
    HasDerivAt (fun r => (A.hamiltonianRenormalizedSourceFlow D le_rfl φ r).val)
      (sourceFiniteGapPhysicalNLSCoefficients (A.hamiltonianRenormalizedSourceFlow D le_rfl φ time)
        (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf time) +
        (4*sourceOrdinaryMass le_rfl φ : ℂ) •
          sourcePhase (A.hamiltonianRenormalizedSourceFlow D le_rfl φ time).val) time := by
  classical
  let S := hf.toFinset
  have hz : ∀ n ∉ S, (sourceComplexBirkhoffMap (by simp) (by norm_num) t φ.val).1 n = 0 ∧
      (sourceComplexBirkhoffMap (by simp) (by norm_num) t φ.val).2 n = 0 := by
    intro n hn
    have hg : sourcePeriodicGapDisplacement (by simp) (by norm_num) φ.val n = 0 := by
      rw [sourcePeriodicGapDisplacement_apply]
      by_contra h
      exact hn (hf.mem_toFinset.mpr h)
    have hh := D.real_closed_gap_zero φ.val (D.real_subset φ.property) φ.property n hg
    simp only [sourceComplexBirkhoffMap,Birkhoff.rectangularToComplex_fst,
      Birkhoff.rectangularToComplex_snd,hh.1,hh.2,mul_zero,sub_zero,add_zero,and_self]
  let ψ := A.hamiltonianRenormalizedSourceFlow D le_rfl φ time
  have hS : ∀ n ∉ S, fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) ψ.val = 0 := by
    intro n hn
    apply sourceComplexAction_fderiv_eq_zero_of_closed_gap (by simp) (by norm_num) ψ.val ψ.property n
    rw [sourcePeriodicGapDisplacement_apply]
    apply A.hamiltonianRenormalizedSourceFlow_closed_gap D φ time n
    by_contra h
    exact hn (hf.mem_toFinset.mpr h)
  have hd := A.hasDerivAt_hamiltonianRenormalizedSourceFlow_autonomous hs D le_rfl le_rfl φ S hz time
  rw [A.finiteActionHamiltonianVector_renormalized_eq ψ S hS,
    A.finiteActionHamiltonianVector_eq_physicalNLS hs D ψ
      (A.hamiltonianRenormalizedSourceFlow_finiteGap D le_rfl φ hf time) S
      (A.complex_support_hamiltonianRenormalizedSourceFlow D le_rfl φ S hz time),
    A.hamiltonianRenormalizedSourceFlow_mass D le_rfl φ time] at hd
  exact hd

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
