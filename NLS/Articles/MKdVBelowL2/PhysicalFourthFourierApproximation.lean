import NLS.Articles.MKdVBelowL2.PhysicalMKdVDiagonal
import NLS.ZakharovShabat.SourceWeightedFiniteSupport

/-! # Native physical H₄ representatives of original Fourier cutoffs

The original distribution functionals are retained in both components.
Finite Fourier support is used only for weighted regularity; the cutoffs
are not asserted to have finitely many spectral gaps.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat NLS.Fourier NLS.Fourier.SmoothPeriodicTest
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every finite Fourier physical real pair has an original native H₄
representative of the same two period-one distribution functionals. -/
theorem exists_nativeFourth_of_physical_finiteSupport
    (u : PhysicalRealInput p)
    (hf : Coeff.HasFiniteSupport (physicalCoefficients u.val).fst ∧
      Coeff.HasFiniteSupport (physicalCoefficients u.val).snd) :
    ∃ a : NativeFourthSobolevSource,
      u.val.1.val = (fourthSobolevPhysicalInput a).val.1.val ∧
      u.val.2.val = (fourthSobolevPhysicalInput a).val.2.val := by
  obtain ⟨a,ha⟩ := exists_weightedRealSource_of_finiteSupport (q := 2)
    fourthSobolevSpectralWeight (physicalRealCoefficientsCL u) hf.1 hf.2
  refine ⟨a,?_,?_⟩
  · apply Distribution.ext_coefficients
    intro n
    exact (physicalCoefficients_apply u.val n).1.symm.trans
      (((ha n).1.symm.trans
        (congrArg (fun φ : CoeffPair 2 => φ.fst n)
          (fourthSobolevPhysicalInput_coefficients a)).symm).trans
        (physicalCoefficients_apply (fourthSobolevPhysicalInput a).val n).1)
  · apply Distribution.ext_coefficients
    intro n
    exact (physicalCoefficients_apply u.val n).2.symm.trans
      (((ha n).2.symm.trans
        (congrArg (fun φ : CoeffPair 2 => φ.snd n)
          (fourthSobolevPhysicalInput_coefficients a)).symm).trans
        (physicalCoefficients_apply (fourthSobolevPhysicalInput a).val n).2)

/-- Each diagonal-preserving Fourier cutoff has the same actual distributions
as a native fractional source, and that source retains equal fields. -/
theorem exists_nativeFourth_physicalMKdVTruncate (N : ℕ) (u : PhysicalMKdVInput p) :
    ∃ a : NativeFourthSobolevSource,
      (physicalMKdVTruncate N u.val).val.1.val = (fourthSobolevPhysicalInput a).val.1.val ∧
      (physicalMKdVTruncate N u.val).val.2.val = (fourthSobolevPhysicalInput a).val.2.val ∧
      fourthSobolevPhysicalInput a ∈ physicalMKdVSubspace 2 := by
  obtain ⟨a,ha,hb⟩ := exists_nativeFourth_of_physical_finiteSupport
    (physicalMKdVTruncate N u.val) (physicalMKdVTruncate_finite N u.val)
  refine ⟨a,ha,hb,?_⟩
  rw [mem_physicalMKdVSubspace_iff]
  apply Subtype.ext
  rw [← ha,← hb]
  exact congrArg Subtype.val ((mem_physicalMKdVSubspace_iff _).mp (physicalMKdVTruncate_mem N u))

end NLS.Articles.MKdVBelowL2
