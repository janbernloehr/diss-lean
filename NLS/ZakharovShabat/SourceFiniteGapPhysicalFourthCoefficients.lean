import NLS.ZakharovShabat.PhysicalFourthCotangent
import NLS.ZakharovShabat.SourceSobolevFourthPhysicalCotangent
import NLS.ZakharovShabat.SourceSobolevFourthFrequencyReality
import NLS.ZakharovShabat.SourceFiniteActionHamiltonian

/-! # The physical fourth Hamiltonian field in the original Hilbert source

The classical smooth finite-gap field is represented by its actual Fourier
integrals. Calibrated complex physical cotangents prove Hilbert membership and
identify it with the finite sum of original action fields weighted by the
independently defined physical H₄ frequencies.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Fourier NLS.Poisson NLS.MKdV
namespace NLS.ZakharovShabat

/-- Every actual real finite-gap source has a native fractional representative
of the same original Fourier fields. -/
theorem exists_nativeFourth_of_sourceFiniteGap (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ a : NativeFourthSobolevSource, originalWeightedRealSource fourthSobolevSpectralWeight a = φ := by
  apply (exists_originalWeightedRealSource_iff fourthSobolevSpectralWeight φ).mpr
  have hm := sourceFiniteGap_mem_all_sobolev (by simp) (by norm_num) φ hf (3/2) (by norm_num)
  simpa only [fourthSobolevSpectralWeight,sourceSobolevSpectralWeight_even] using hm

/-- The independently defined physical third-order field at the actual
smooth finite-gap representative. -/
def sourceFiniteGapPhysicalFourthVectorField (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) : (ℝ → ℂ) × (ℝ → ℂ) :=
  classicalNLSFourthVectorField (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1
    (sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).2

/-- The physical field as an original Hilbert source, with its coefficient
recovery proved below rather than assumed of the total constructor. -/
def sourceFiniteGapPhysicalFourthCoefficients (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) : CoeffPair 2 :=
  (CoeffPair.toMax 2).symm
    (Coeff.ofFunctionOrZero 2 (periodOneCoefficient (sourceFiniteGapPhysicalFourthVectorField φ hf).1),
      Coeff.ofFunctionOrZero 2 (periodOneCoefficient (sourceFiniteGapPhysicalFourthVectorField φ hf).2))

/-- The original Poisson direction of any calibrated physical H₄ cotangent
has exactly the actual smooth finite-gap physical Fourier integrals. -/
theorem sourceHamiltonianDirection_finiteGapPhysicalFourth_coordinates
    (a : NativeFourthSobolevSource)
    (hf : originalWeightedRealSource fourthSobolevSpectralWeight a ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (L : CoeffPair 2 →L[ℂ] ℂ)
    (hL : HasFDerivAt sourceComplexSobolevFourthHamiltonian
      (L.comp (originalWeightedSourceCLM fourthSobolevSpectralWeight)) a.val) (n : ℤ) :
    (sourceHamiltonianDirection le_rfl L).fst n = periodOneCoefficient
      (sourceFiniteGapPhysicalFourthVectorField (originalWeightedRealSource fourthSobolevSpectralWeight a) hf).1 n ∧
    (sourceHamiltonianDirection le_rfl L).snd n = periodOneCoefficient
      (sourceFiniteGapPhysicalFourthVectorField (originalWeightedRealSource fourthSobolevSpectralWeight a) hf).2 n := by
  let φ := originalWeightedRealSource fourthSobolevSpectralWeight a
  exact sourceHamiltonianDirection_physicalFourth_coordinates a.val _ _
    (contDiff_sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1
    (contDiff_sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).2
    (periodic_sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).1
    (periodic_sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf).2
    (fun k => (originalWeightedRealSource_fst fourthSobolevSpectralWeight a k).symm.trans
      (periodOneCoefficient_sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf k).1.symm)
    (fun k => (originalWeightedRealSource_snd fourthSobolevSpectralWeight a k).symm.trans
      (periodOneCoefficient_sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf k).2.symm) L hL n

/-- A calibrated physical cotangent gives the entire original source field,
so the Fourier-integral constructor really is Hilbert summable. -/
theorem sourceFiniteGapPhysicalFourthCoefficients_eq_HamiltonianDirection
    (a : NativeFourthSobolevSource)
    (hf : originalWeightedRealSource fourthSobolevSpectralWeight a ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (L : CoeffPair 2 →L[ℂ] ℂ)
    (hL : HasFDerivAt sourceComplexSobolevFourthHamiltonian
      (L.comp (originalWeightedSourceCLM fourthSobolevSpectralWeight)) a.val) :
    sourceFiniteGapPhysicalFourthCoefficients (originalWeightedRealSource fourthSobolevSpectralWeight a) hf =
      sourceHamiltonianDirection le_rfl L := by
  have he := sourceHamiltonianDirection_finiteGapPhysicalFourth_coordinates a hf L hL
  apply (CoeffPair.toMax 2).injective
  exact Prod.ext (Coeff.ofFunctionOrZero_eq_of_coordinates _ _ (fun n => (he n).1))
    (Coeff.ofFunctionOrZero_eq_of_coordinates _ _ (fun n => (he n).2))

/-- Every coefficient of the constructed Hilbert source is the original
physical Fourier integral, for every actual real finite-gap source. -/
theorem sourceFiniteGapPhysicalFourthCoefficients_apply
    (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) :
    (sourceFiniteGapPhysicalFourthCoefficients φ hf).fst n =
      periodOneCoefficient (sourceFiniteGapPhysicalFourthVectorField φ hf).1 n ∧
    (sourceFiniteGapPhysicalFourthCoefficients φ hf).snd n =
      periodOneCoefficient (sourceFiniteGapPhysicalFourthVectorField φ hf).2 n := by
  obtain ⟨a,rfl⟩ := exists_nativeFourth_of_sourceFiniteGap φ hf
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  obtain ⟨L,hL⟩ := D.exists_sourceSobolevFourth_finiteGap_physical_cotangent a hf
  rw [sourceFiniteGapPhysicalFourthCoefficients_eq_HamiltonianDirection a hf L hL]
  exact sourceHamiltonianDirection_finiteGapPhysicalFourth_coordinates a hf L hL n

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The actual physical fourth field is exactly the finite sum of original
action Hamiltonian fields with independent physical H₄ frequencies. -/
theorem finiteActionHamiltonianVector_eq_physicalFourth
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource)
    (hf : originalWeightedRealSource fourthSobolevSpectralWeight a ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (S : Finset ℤ)
    (hS : ∀ n ∉ S, fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val = 0) :
    sourceFiniteActionHamiltonianVector (by simp) (by norm_num) le_rfl
      (fun n => (D.sobolevFourthFrequency a n).re) S (originalWeightedRealSource fourthSobolevSpectralWeight a).val =
      sourceFiniteGapPhysicalFourthCoefficients (originalWeightedRealSource fourthSobolevSpectralWeight a) hf := by
  let L : CoeffPair 2 →L[ℂ] ℂ := ∑ n ∈ S, D.sobolevFourthFrequency a n •
    fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n)
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val
  have hL : HasFDerivAt sourceComplexSobolevFourthHamiltonian
      (L.comp (originalWeightedSourceCLM fourthSobolevSpectralWeight)) a.val :=
    D.sourceComplexSobolevFourthHamiltonian_fderiv_eq_finite_sum a S hS ▸
      (analyticAt_sourceComplexSobolevFourthHamiltonian a.val).differentiableAt.hasFDerivAt
  rw [sourceFiniteGapPhysicalFourthCoefficients_eq_HamiltonianDirection a hf L hL]
  simp only [L,map_sum,map_smul,sourceFiniteActionHamiltonianVector,sourceHamiltonianVector]
  apply Finset.sum_congr rfl
  intro n _
  rw [D.sobolevFourthFrequency_ofReal_re]

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
