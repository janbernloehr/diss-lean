import NLS.Poisson.HminusGardnerBracket
import NLS.SequenceSpaces.HminusMeanZeroProjection
import NLS.SequenceSpaces.ComplexMeanZeroWeighted

/-! # The original Gardner bracket on the complex mean-zero space

Deleting the central Fourier mode preserves the physical Gardner bracket.
Thus the bracket of functions on the closed mean-zero space is intrinsic.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.Poisson

/-- The Gardner bracket of functions on the actual closed complex mean-zero space. -/
def meanZeroHminusGardnerBracket
    (F G : complexMeanZeroWeightedSubmodule (Weight.sobolev (-1)) → ℂ)
    (q : complexMeanZeroWeightedSubmodule (Weight.sobolev (-1))) : ℂ :=
  hminusGardnerBracket
    (fun u => F (complexMeanZeroWeightedProjection (Weight.sobolev (-1)) u))
    (fun u => G (complexMeanZeroWeightedProjection (Weight.sobolev (-1)) u)) q.val

theorem hminusScalarGradient_comp_meanZeroProjection_other
    (F : PeriodOneHminusOne → ℂ) (q : PeriodOneHminusOne) (hm : q.val 0 = 0)
    (hF : DifferentiableAt ℂ F q) (k : ℤ) (hk : k ≠ 0) :
    (hminusScalarGradient (fun u => F (hminusMeanZeroProjection u)) q).val k =
      (hminusScalarGradient F q).val k := by
  have hQ := hminusMeanZeroProjection_eq_self q hm
  have hd := ((hF.hasFDerivAt : HasFDerivAt F (fderiv ℂ F q) q))
  rw [←hQ] at hd
  have he : fderiv ℂ (fun u => F (hminusMeanZeroProjection u)) q =
      (fderiv ℂ F q).comp hminusMeanZeroProjection := by
    simpa only [Function.comp_def,hQ] using! (hd.comp q hminusMeanZeroProjection.hasFDerivAt).fderiv
  let e := WeightedCoeff.ofFinsupp (Weight.sobolev (-1)) 2 (Finsupp.single (-k) 1)
  have hQe : hminusMeanZeroProjection e = e := by
    apply hminusMeanZeroProjection_eq_self
    change Finsupp.single (-k) (1 : ℂ) 0 = 0
    exact Finsupp.single_eq_of_ne (neg_ne_zero.mpr hk).symm
  have hh := congrArg (fun L : PeriodOneHminusOne →L[ℂ] ℂ => L e) he
  rw [hminusScalarGradient_apply,hminusScalarGradient_apply]
  simpa only [ContinuousLinearMap.comp_apply,hQe] using! hh

/-- Literal zero-mode deletion does not change the actual physical bracket. -/
theorem hminusGardnerBracket_comp_meanZeroProjection
    (F G : PeriodOneHminusOne → ℂ) (q : PeriodOneHminusOne) (hm : q.val 0 = 0)
    (hF : DifferentiableAt ℂ F q) (hG : DifferentiableAt ℂ G q) :
    hminusGardnerBracket (fun u => F (hminusMeanZeroProjection u))
      (fun u => G (hminusMeanZeroProjection u)) q = hminusGardnerBracket F G q := by
  unfold hminusGardnerBracket
  rw [gardnerBivector_eq_tsum,gardnerBivector_eq_tsum]
  apply tsum_congr
  intro k
  by_cases hk : k = 0
  · subst k
    simp
  · rw [hminusScalarGradient_comp_meanZeroProjection_other F q hm hF k hk,
      hminusScalarGradient_comp_meanZeroProjection_other G q hm hG (-k) (neg_ne_zero.mpr hk)]

end NLS.Poisson
