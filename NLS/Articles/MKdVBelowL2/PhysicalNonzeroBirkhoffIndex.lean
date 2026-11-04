import NLS.Articles.MKdVBelowL2.PhysicalFourthImageIdentities
import NLS.ZakharovShabat.SourceBirkhoffNonzeroIndex

/-! # A nonzero signed physical Birkhoff mode outside the Hilbert domain

Being in the physical Hilbert space means that the same original pair of
period-one distributions is represented by a real FL² input. Finite spectral
gap support supplies exactly such a representative. Consequently a physical
pair outside that space has a nonzero first Birkhoff mode at n≠0.
-/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat NLS.Fourier NLS.Fourier.SmoothPeriodicTest
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Membership in the original physical Hilbert pair space, with the
original distribution functionals unchanged in both components. -/
def physicalPairHasHilbertRepresentative (u : PhysicalRealInput p) : Prop :=
  ∃ v : PhysicalRealInput 2, u.val.1.val = v.val.1.val ∧ u.val.2.val = v.val.2.val

/-- Actual spectral finite-gap regularity gives an actual physical Hilbert
representative of both distributions, rather than only equal spectral data. -/
theorem physicalPairHasHilbertRepresentative_of_finiteGap
    (hp : p ≠ ⊤) (hp1 : 1 < p) (u : PhysicalRealInput p)
    (hf : physicalRealCoefficientsCL u ∈ sourceFiniteGapLocus hp hp1) :
    physicalPairHasHilbertRepresentative u := by
  let φ := physicalRealCoefficientsCL u
  let ψ := sourceFiniteGapHilbertModel hp hp1 φ hf
  let v := (physicalRealCoefficientsCL (p := 2)).symm ψ
  have hv : physicalCoefficients v.val = ψ.val := by
    rw [← physicalRealCoefficientsCL_val]
    exact congrArg Subtype.val ((physicalRealCoefficientsCL (p := 2)).apply_symm_apply ψ)
  have hcoeff (n : ℤ) : (physicalCoefficients v.val).fst n = (physicalCoefficients u.val).fst n ∧
      (physicalCoefficients v.val).snd n = (physicalCoefficients u.val).snd n := by
    rw [hv]
    exact sourceFiniteGapHilbertModel_coefficients hp hp1 φ hf n
  refine ⟨v,?_,?_⟩
  · apply Distribution.ext_coefficients
    intro n
    exact ((physicalCoefficients_apply u.val n).1.symm.trans
      ((hcoeff n).1.symm.trans (physicalCoefficients_apply v.val n).1))
  · apply Distribution.ext_coefficients
    intro n
    exact ((physicalCoefficients_apply u.val n).2.symm.trans
      ((hcoeff n).2.symm.trans (physicalCoefficients_apply v.val n).2))

/-- Every real physical input outside FL² has a nonzero first Birkhoff mode
at a nonzero signed index. This is the mode required for the fixed-time
mass-phase obstruction; no assertion at the degenerate index zero is used. -/
theorem exists_nonzero_physical_birkhoff_index
    (hp : p ≠ ⊤) (hp1 : 1 < p) (u : PhysicalRealInput p)
    (hu : ¬ physicalPairHasHilbertRepresentative u) :
    ∃ n : ℤ, n ≠ 0 ∧ (compatibleBirkhoff hp hp1 u.val).1 n ≠ 0 := by
  classical
  by_contra! h
  apply hu
  apply physicalPairHasHilbertRepresentative_of_finiteGap hp hp1 u
  apply (originalBirkhoffChart hp hp1).data.complex.finiteGap_of_complex_fst_vanishes_off
    (physicalRealCoefficientsCL u) {0}
  intro n hn
  exact h n (by simpa only [Finset.mem_singleton] using hn)

end NLS.Articles.MKdVBelowL2
