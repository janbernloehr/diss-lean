import NLS.KdV.HillRoughSignedDerivativeComponents
import NLS.Articles.KdVKdV2Frequencies.FiniteActionCoordinateRotations

/-! # An actual rough curve derivative is the physical finite action vector

The coordinate rotation identities are compared with the genuine chain
rule of the supplied curve. Injectivity of the full actual mean-zero
rough differential identifies the entire original source direction.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem curve_derivative_eq_finiteActionVector (D : GlobalRoughAbelianForwardData)
    (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2))
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (m : ℝ))) (S : Finset ℕ+)
    (U : ℝ → PeriodOneHminusOne) (t : ℝ) (v : PeriodOneHminusOne)
    (hU : HasDerivAt U v t) (hr : IsRealPeriodOneHminusOne (U t))
    (hm : (U t).val 0=0) (hv : v.val 0=0)
    (hcomp : ∀ σ : Bool, ∀ n : ℕ+,
      HasDerivAt (fun u : ℝ => hillRoughSignedAbelianComponent D.signed σ n (U u))
        (if n∈S then (D.nativeSourceHierarchyFrequency m r hrs q n : ℂ)*
          (if σ then I else -I)*hillRoughSignedAbelianComponent D.signed σ n (U t) else 0) t) :
    v=NLS.Poisson.gardnerHamiltonianVector (D.finiteGapActionCombination m r hrs q S) (U t) := by
  let V := NLS.Poisson.gardnerHamiltonianVector (D.finiteGapActionCombination m r hrs q S) (U t)
  have hV : V.val 0=0 := NLS.Poisson.gardnerHamiltonianDirection_zero_mode _
  apply D.meanZero_direction_eq_of_signed_components (U t) hr hm v V hv hV
  intro σ n
  have hG := hillRoughSignedAbelianComponent_analytic D.signed D.signed_analytic σ n
    (U t) (D.real_mem_domain _ hr)
  have hchain := (hG.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hU
  have he := hchain.unique (hcomp σ n)
  change (fderiv ℂ (hillRoughSignedAbelianComponent D.signed σ n) (U t)) v=_ at he
  rw [he]
  exact (D.signedComponent_fderiv_finiteActionVector m r hrs q S (U t)
    (D.real_meanZero_mem_canonicalDomain _ hr hm) hm σ n).symm

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
