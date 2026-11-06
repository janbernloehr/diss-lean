import NLS.Articles.KdVKdV2Frequencies.GlobalRawIntegerInverse
import NLS.KdV.NativeHamiltonianPhysicalIntegrals
import NLS.KdV.NativeHamiltonianReality

/-! # Actual global native Hamiltonians in the SAME Birkhoff coordinates

The raw target domains are exactly the physical real mean-zero h^(3/2)
and h^(5/2) spaces. The original physical H1 and H2 are evaluated at the
SAME already-fixed global weak inverse restricted to the native source.
They are real analytic everywhere in these original raw native norms.
Analytic factorization through actions remains a separate obligation.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- The ORIGINAL physical KdV Hamiltonian composed with the SAME global
inverse on the entire ACTUAL raw real h^(3/2) target. -/
def birkhoffKdVHamiltonian (D : GlobalRoughAbelianForwardData)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((1 : ℕ) : ℝ)+1/2))) : ℝ :=
  (nativeKdVHamiltonian (D.rawIntegerInverseSource 1 z)).re

/-- The ORIGINAL physical KdV2 Hamiltonian composed with the SAME global
inverse on the entire ACTUAL raw real h^(5/2) target. -/
def birkhoffKdV2Hamiltonian (D : GlobalRoughAbelianForwardData)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((2 : ℕ) : ℝ)+1/2))) : ℝ :=
  (nativeKdV2Hamiltonian (D.rawIntegerInverseSource 2 z)).re

/-- Real analyticity at EVERY actual h^(3/2) target in its original norm,
including arbitrary size, infinite support and all closed gaps. -/
theorem birkhoffKdVHamiltonian_analytic (D : GlobalRoughAbelianForwardData) :
    AnalyticOnNhd ℝ D.birkhoffKdVHamiltonian univ := by
  intro z _
  have hs := D.rawIntegerInverseSource_analytic 1 z (mem_univ _)
  have hH := (analyticAt_nativeKdVHamiltonian (D.rawIntegerInverseSource 1 z)).restrictScalars (𝕜 := ℝ)
  exact (Complex.reCLM.analyticAt _).comp
    (hH.comp (f := D.rawIntegerInverseSource 1) hs)

/-- Real analyticity at EVERY actual h^(5/2) target in its original norm,
including arbitrary size, infinite support and all closed gaps. -/
theorem birkhoffKdV2Hamiltonian_analytic (D : GlobalRoughAbelianForwardData) :
    AnalyticOnNhd ℝ D.birkhoffKdV2Hamiltonian univ := by
  intro z _
  have hs := D.rawIntegerInverseSource_analytic 2 z (mem_univ _)
  have hH := (analyticAt_nativeKdV2Hamiltonian (D.rawIntegerInverseSource 2 z)).restrictScalars (𝕜 := ℝ)
  exact (Complex.reCLM.analyticAt _).comp
    (hH.comp (f := D.rawIntegerInverseSource 2) hs)

/-- No imaginary part is discarded by the real-valued formulation. -/
theorem birkhoffKdVHamiltonian_complex_value (D : GlobalRoughAbelianForwardData)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((1 : ℕ) : ℝ)+1/2))) :
    (D.birkhoffKdVHamiltonian z : ℂ)=nativeKdVHamiltonian (D.rawIntegerInverseSource 1 z) := by
  apply Complex.ext
  · rfl
  · exact (nativeKdVHamiltonian_im_eq_zero _ (D.rawIntegerInverseSource_real 1 z)).symm

theorem birkhoffKdV2Hamiltonian_complex_value (D : GlobalRoughAbelianForwardData)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((2 : ℕ) : ℝ)+1/2))) :
    (D.birkhoffKdV2Hamiltonian z : ℂ)=nativeKdV2Hamiltonian (D.rawIntegerInverseSource 2 z) := by
  apply Complex.ext
  · rfl
  · exact (nativeKdV2Hamiltonian_im_eq_zero _ (D.rawIntegerInverseSource_real 2 z)).symm

/-- Exact physical unit-period integral at the SAME globally recovered
H1 source, for EVERY actual raw native target. -/
theorem birkhoffKdVHamiltonian_eq_physical (D : GlobalRoughAbelianForwardData)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((1 : ℕ) : ℝ)+1/2))) :
    (D.birkhoffKdVHamiltonian z : ℂ)=classicalHamiltonian
      (fun x : ℝ => (hierarchySobolevJetContinuous 1 0 (by omega)
        (D.rawIntegerInverseSource 1 z)) (x : AddCircle (2 : ℝ))) :=
  (D.birkhoffKdVHamiltonian_complex_value z).trans (nativeKdVHamiltonian_eq_classical _)

/-- Exact physical unit-period integral at the SAME globally recovered
H2 source, with ALL printed coefficients and actual derivatives retained. -/
theorem birkhoffKdV2Hamiltonian_eq_physical (D : GlobalRoughAbelianForwardData)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((2 : ℕ) : ℝ)+1/2))) :
    (D.birkhoffKdV2Hamiltonian z : ℂ)=classicalKdV2Hamiltonian
      (fun x : ℝ => (hierarchySobolevJetContinuous 2 0 (by omega)
        (D.rawIntegerInverseSource 2 z)) (x : AddCircle (2 : ℝ))) :=
  (D.birkhoffKdV2Hamiltonian_complex_value z).trans (nativeKdV2Hamiltonian_eq_classical _)

/-- Full signed matching identifies this Hamiltonian with the ORIGINAL
native Hamiltonian at ANY given real mean-zero H1 source. -/
theorem birkhoffKdVHamiltonian_eq_native_of_signed_eq (D : GlobalRoughAbelianForwardData)
    (q : ScalarSobolev 1) (hq : ∀ n : ℤ, q.val (-n)=conj (q.val n)) (hm : q.val 0=0)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((1 : ℕ) : ℝ)+1/2)))
    (h : D.signed (WeightedCoeff.sobolevInclusion (by norm_num : (-1 : ℝ)≤((1 : ℕ) : ℝ)) q)=
      WeightedCoeff.sobolevInclusion (by norm_num : (-1/2 : ℝ)≤((1 : ℕ) : ℝ)+1/2) z.val) :
    (D.birkhoffKdVHamiltonian z : ℂ)=nativeKdVHamiltonian q := by
  rw [D.birkhoffKdVHamiltonian_complex_value,D.rawIntegerInverseSource_eq_of_signed_eq 1 q hq hm z h]

theorem birkhoffKdV2Hamiltonian_eq_native_of_signed_eq (D : GlobalRoughAbelianForwardData)
    (q : ScalarSobolev 2) (hq : ∀ n : ℤ, q.val (-n)=conj (q.val n)) (hm : q.val 0=0)
    (z : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (((2 : ℕ) : ℝ)+1/2)))
    (h : D.signed (WeightedCoeff.sobolevInclusion (by norm_num : (-1 : ℝ)≤((2 : ℕ) : ℝ)) q)=
      WeightedCoeff.sobolevInclusion (by norm_num : (-1/2 : ℝ)≤((2 : ℕ) : ℝ)+1/2) z.val) :
    (D.birkhoffKdV2Hamiltonian z : ℂ)=nativeKdV2Hamiltonian q := by
  rw [D.birkhoffKdV2Hamiltonian_complex_value,D.rawIntegerInverseSource_eq_of_signed_eq 2 q hq hm z h]

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
