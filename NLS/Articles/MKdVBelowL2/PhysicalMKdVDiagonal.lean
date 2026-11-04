import NLS.Articles.MKdVBelowL2.FourthHamiltonianPhaseFamily
import NLS.ZakharovShabat.SourceComponentSwap
import NLS.ZakharovShabat.SourceSobolevFourthDiagonal
import NLS.ZakharovShabat.SourceSymmetricTruncate

/-! # The actual real physical mKdV diagonal

This closed Banach subspace consists of equal original distribution fields
inside the NLS real form. Fourier uniqueness identifies it with the literal
unsigned-component-swap fixed source slice. Symmetric Fourier truncations
preserve this diagonal and converge in its original finite-exponent norm.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat NLS.Fourier NLS.Fourier.SmoothPeriodicTest
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Difference of the two actual physical distribution fields. -/
def physicalComponentDifferenceCLM (p : ℝ≥0∞) [Fact (1 ≤ p)] : PhysicalRealInput p →L[ℝ] PhysicalFL p :=
  (((ContinuousLinearMap.fst ℂ (PhysicalFL p) (PhysicalFL p))-
    (ContinuousLinearMap.snd ℂ (PhysicalFL p) (PhysicalFL p))).restrictScalars ℝ).comp
      (physicalRealSubspace p).subtypeL

/-- The true real mKdV diagonal, with its inherited physical Fourier norm. -/
def physicalMKdVSubspace (p : ℝ≥0∞) [Fact (1 ≤ p)] : Submodule ℝ (PhysicalRealInput p) :=
  (physicalComponentDifferenceCLM p).ker

/-- Actual scalar real mKdV data represented by their equal physical pair. -/
abbrev PhysicalMKdVInput (p : ℝ≥0∞) [Fact (1 ≤ p)] := ↥(physicalMKdVSubspace p)

/-- Diagonal membership compares the actual distributions, not spectral data. -/
theorem mem_physicalMKdVSubspace_iff (u : PhysicalRealInput p) :
    u ∈ physicalMKdVSubspace p ↔ u.val.1 = u.val.2 := by
  change u.val.1-u.val.2 = 0 ↔ _
  exact sub_eq_zero

/-- The actual physical mKdV diagonal is closed. -/
theorem isClosed_physicalMKdVSubspace :
    IsClosed (physicalMKdVSubspace p : Set (PhysicalRealInput p)) :=
  (physicalComponentDifferenceCLM p).isClosed_ker

instance physicalMKdVInputCompleteSpace : CompleteSpace (PhysicalMKdVInput p) :=
  isClosed_physicalMKdVSubspace.completeSpace_coe

/-- Fourier uniqueness identifies the physical diagonal with equal original
source coefficients in the two components, at every Banach exponent. -/
theorem mem_physicalMKdVSubspace_iff_source (u : PhysicalRealInput p) :
    u ∈ physicalMKdVSubspace p ↔ (physicalRealCoefficientsCL u).val.fst =
      (physicalRealCoefficientsCL u).val.snd := by
  rw [mem_physicalMKdVSubspace_iff]
  constructor
  · intro h
    apply lp.ext
    funext n
    change (physicalCoefficients u.val).fst n = (physicalCoefficients u.val).snd n
    rw [(physicalCoefficients_apply u.val n).1,(physicalCoefficients_apply u.val n).2,h]
  · intro h
    apply Subtype.ext
    apply Distribution.ext_coefficients
    intro n
    exact (physicalCoefficients_apply u.val n).1.symm.trans
      ((congrArg (fun a : Coeff p => a n) h).trans (physicalCoefficients_apply u.val n).2)

/-- The actual physical diagonal is the unsigned-component-swap fixed source
slice, distinguishing it from midpoint spatial-reflection symmetry. -/
theorem mem_physicalMKdVSubspace_iff_componentSwap (u : PhysicalRealInput p) :
    u ∈ physicalMKdVSubspace p ↔ sourceComponentSwap (physicalRealCoefficientsCL u).val =
      (physicalRealCoefficientsCL u).val :=
  (mem_physicalMKdVSubspace_iff_source u).trans (sourceComponentSwap_eq_self_iff _).symm

/-- Physical symmetric Fourier truncation, retaining the original real form. -/
def physicalMKdVTruncate (N : ℕ) (u : PhysicalRealInput p) : PhysicalRealInput p :=
  physicalRealCoefficientsCL.symm
    ⟨sourceSymmetricTruncate N (physicalRealCoefficientsCL u).val,
      sourceSymmetricTruncate_realType N _ (physicalRealCoefficientsCL u).property⟩

/-- Every symmetric Fourier cutoff preserves the true physical mKdV diagonal. -/
theorem physicalMKdVTruncate_mem (N : ℕ) (u : PhysicalMKdVInput p) :
    physicalMKdVTruncate N u.val ∈ physicalMKdVSubspace p := by
  rw [mem_physicalMKdVSubspace_iff_source]
  have he : physicalRealCoefficientsCL (physicalMKdVTruncate N u.val) =
      ⟨sourceSymmetricTruncate N (physicalRealCoefficientsCL u.val).val,
        sourceSymmetricTruncate_realType N _ (physicalRealCoefficientsCL u.val).property⟩ :=
    physicalRealCoefficientsCL.apply_symm_apply _
  rw [he]
  change Coeff.truncate (Finset.Icc (-(N:ℤ)) N) (physicalRealCoefficientsCL u.val).val.fst =
    Coeff.truncate (Finset.Icc (-(N:ℤ)) N) (physicalRealCoefficientsCL u.val).val.snd
  rw [(mem_physicalMKdVSubspace_iff_source u.val).mp u.property]

/-- The physical diagonal cutoffs have actual finite Fourier support in
both original components; no spectral finite-gap assertion is inserted. -/
theorem physicalMKdVTruncate_finite (N : ℕ) (u : PhysicalRealInput p) :
    Coeff.HasFiniteSupport (physicalCoefficients (physicalMKdVTruncate N u).val).fst ∧
      Coeff.HasFiniteSupport (physicalCoefficients (physicalMKdVTruncate N u).val).snd := by
  have he : physicalRealCoefficientsCL (physicalMKdVTruncate N u) =
      ⟨sourceSymmetricTruncate N (physicalRealCoefficientsCL u).val,
        sourceSymmetricTruncate_realType N _ (physicalRealCoefficientsCL u).property⟩ :=
    physicalRealCoefficientsCL.apply_symm_apply _
  change Coeff.HasFiniteSupport (physicalRealCoefficientsCL (physicalMKdVTruncate N u)).val.fst ∧
    Coeff.HasFiniteSupport (physicalRealCoefficientsCL (physicalMKdVTruncate N u)).val.snd
  rw [he]
  exact sourceSymmetricTruncate_finite N _

/-- Fourier cutoffs converge in the actual physical source norm at every
finite exponent, preserving the diagonal when applied to mKdV data. -/
theorem tendsto_physicalMKdVTruncate (hp : p ≠ ⊤) (u : PhysicalRealInput p) :
    Tendsto (fun N : ℕ => physicalMKdVTruncate N u) atTop (𝓝 u) := by
  have hsrc : Tendsto (fun N : ℕ => (⟨sourceSymmetricTruncate N (physicalRealCoefficientsCL u).val,
      sourceSymmetricTruncate_realType N _ (physicalRealCoefficientsCL u).property⟩ : realTypeSourceSubmodule p))
      atTop (𝓝 (physicalRealCoefficientsCL u)) :=
    tendsto_subtype_rng.mpr (tendsto_sourceSymmetricTruncate hp (physicalRealCoefficientsCL u).val)
  have h : Tendsto (fun N : ℕ => physicalMKdVTruncate N u) atTop
      (𝓝 (physicalRealCoefficientsCL.symm (physicalRealCoefficientsCL u))) :=
    physicalRealCoefficientsCL.symm.continuous.continuousAt.tendsto.comp hsrc
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using h

/-- On the full original fractional physical diagonal, the rotation frequency
is the actual H₄ derivative minus only the mass-dependent translation shift. -/
theorem fourthSourcePhaseFrequency_eq_mKdV_derivative
    (a : NativeFourthSobolevSource) (ha : fourthSobolevPhysicalInput a ∈ physicalMKdVSubspace 2) (n : ℤ) :
    ((fourthSourcePhaseFrequency (p := 2) (by simp) (by norm_num)).frequency
      (originalWeightedRealSource fourthSobolevSpectralWeight a) n : ℂ) =
      (originalBirkhoffChart (p := 2) (by simp) (by norm_num)).data.complex.sobolevFourthFrequency a n-
        (12*Real.pi:ℂ)*n*sourceFourthSobolevMass a := by
  have he : physicalCoefficients (fourthSobolevPhysicalInput a).val =
      (originalWeightedRealSource fourthSobolevSpectralWeight a).val := fourthSobolevPhysicalInput_coefficients a
  have hdiag := (mem_physicalMKdVSubspace_iff_source (fourthSobolevPhysicalInput a)).mp ha
  change (physicalCoefficients (fourthSobolevPhysicalInput a).val).fst =
    (physicalCoefficients (fourthSobolevPhysicalInput a).val).snd at hdiag
  rw [he] at hdiag
  rw [fourthSourcePhaseFrequency_eq_physical_derivative,
    sourceFourthSobolevMomentum_eq_zero_of_diagonal a hdiag,mul_zero,sub_zero]

end NLS.Articles.MKdVBelowL2
