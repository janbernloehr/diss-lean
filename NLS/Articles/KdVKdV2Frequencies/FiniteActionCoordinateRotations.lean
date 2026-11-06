import NLS.Articles.KdVKdV2Frequencies.FiniteGapRoughFirstVariation
import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianComplexCanonical
import NLS.Poisson.HminusGardnerAlgebra

/-! # Intrinsic frequencies in actual signed-coordinate Hamiltonian derivatives

The same global rough coordinates and their proved Gardner matrix give the
rotation law for the genuine finite action functional. Together with the
physical first-jet comparison, this identifies the coordinate motion of its
Hamiltonian vector without assuming a frequency or rotation identity.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- The literal original action generates the signed coordinate rotation,
with the unit-period Gardner normalization, on the common complex domain. -/
theorem signedComponent_fderiv_actionVector (D : GlobalRoughAbelianForwardData)
    (u : PeriodOneHminusOne) (hu : u ∈ D.canonicalDomain) (hm : u.val 0=0)
    (σ : Bool) (n k : ℕ+) :
    (fderiv ℂ (hillRoughSignedAbelianComponent D.signed σ n) u)
      (NLS.Poisson.gardnerHamiltonianVector (D.roughActionCoordinate k) u) =
      if n=k then (if σ then I else -I)*hillRoughSignedAbelianComponent D.signed σ n u else 0 := by
  rw [NLS.Poisson.fderiv_apply_gardnerHamiltonianVector]
  change NLS.Poisson.hminusGardnerBracket _
    (fun v => hillRoughSignedAbelianComponent D.signed true k v *
      hillRoughSignedAbelianComponent D.signed false k v) u = _
  have hd (τ : Bool) := (hillRoughSignedAbelianComponent_analytic D.signed D.signed_analytic τ k
    u (D.canonicalDomain_subset_domain hu)).differentiableAt
  rw [NLS.Poisson.hminusGardnerBracket_mul_right _ _ _ u (hd true) (hd false),
    D.gardner_matrix_complex_meanZero u hu hm σ false n k,
    D.gardner_matrix_complex_meanZero u hu hm σ true n k]
  by_cases h : n=k
  · subst k
    cases σ <;> simp [hillOriginalComplexGardnerMatrixEntry] <;> ring
  · have hnk : (n : ℕ) ≠ (k : ℕ) := fun he => h (Subtype.ext he)
    simp [hillOriginalComplexGardnerMatrixEntry,hnk,h]

/-- Actual finite Hamiltonian vectors rotate the SAME signed coordinates at
exactly the intrinsic physical hierarchy frequencies in the finite support. -/
theorem signedComponent_fderiv_finiteActionVector (D : GlobalRoughAbelianForwardData)
    (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (S : Finset ℕ+)
    (u : PeriodOneHminusOne) (hu : u ∈ D.canonicalDomain) (hm : u.val 0=0)
    (σ : Bool) (n : ℕ+) :
    (fderiv ℂ (hillRoughSignedAbelianComponent D.signed σ n) u)
      (NLS.Poisson.gardnerHamiltonianVector (D.finiteGapActionCombination m r hrs q S) u) =
      if n ∈ S then (D.nativeSourceHierarchyFrequency m r hrs q n : ℂ)*
        (if σ then I else -I)*hillRoughSignedAbelianComponent D.signed σ n u else 0 := by
  rw [D.finiteGapActionCombination_hamiltonianVector m r hrs q S u
    (D.canonicalDomain_subset_domain hu)]
  simp only [map_sum,map_smul,smul_eq_mul,D.signedComponent_fderiv_actionVector u hu hm]
  simp [mul_ite,mul_assoc]

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
