import NLS.KdV.HillHminusEndpointConjugateCommutation
import NLS.KdV.HillHminusSignedCartesianGardnerLimits

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- The actual complex Gardner matrix for the original `Z` convention:
{Z,Z}=0, {Z,bar Z}=2i, {bar Z,Z}=-2i, {bar Z,bar Z}=0. -/
def hillOriginalComplexGardnerMatrixEntry (σ τ : Bool) (n m : ℕ+) : ℂ :=
  (if σ then (if τ then 0 else 2*I) else (if τ then -(2*I) else 0)) *
    (if (n:ℕ)=(m:ℕ) then 1 else 0)

/-- ALL FOUR original complex Cartesian Gardner entries, with their exact
physical signs and normalization, hold at EVERY original all-periodic
source. Only the two selected gaps must be open, and every analytic
H-minus-one representative matching the ORIGINAL real L2 germ is allowed. -/
theorem hillSignedCartesians_hminus_Gardner_endpoint_matrix
    (q : RealPeriodOneHillPotential) (n m : ℕ+) (σ τ : Bool)
    (hgapn : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (hgapm : hillRealGapHalfLength q.val q.property.1 q.property.2 m ≠ 0)
    (hterminal : ∀ k : ℕ, ∀ hk : 1 ≤ k,
      hillDirichletLogMultiplier q.val q.property.1 q.property.2 k hk = 0)
    (F G : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hG : AnalyticAt ℂ G (hillOriginalHminusSource q.val))
    (hFM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p)
    (hGM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian τ m p) :
    NLS.Poisson.hminusGardnerBracket F G (hillOriginalHminusSource q.val) =
      hillOriginalComplexGardnerMatrixEntry σ τ n m := by
  unfold hillOriginalComplexGardnerMatrixEntry
  cases σ <;> cases τ
  · simpa using hillOriginalConjugateCartesians_hminus_Gardner_endpoint_zero
      q n m hgapn hgapm hterminal F G hF hG hFM hGM
  · rw [NLS.Poisson.hminusGardnerBracket_antisymm,
      hillOriginalCartesian_conjugate_hminus_Gardner_endpoint_eq q m n hgapm hgapn hterminal
        G F hG hF hGM hFM]
    change -(2 * I * (if (m:ℕ)=(n:ℕ) then 1 else 0 : ℂ)) =
      -(2 * I) * (if (n:ℕ)=(m:ℕ) then 1 else 0 : ℂ)
    by_cases hnm : (n:ℕ)=(m:ℕ)
    · rw [if_pos hnm.symm,if_pos hnm]
      ring
    · rw [if_neg (Ne.symm hnm),if_neg hnm]
      ring
  · simpa using hillOriginalCartesian_conjugate_hminus_Gardner_endpoint_eq
      q n m hgapn hgapm hterminal F G hF hG hFM hGM
  · simpa using hillOriginalCartesians_hminus_Gardner_endpoint_zero
      q n m hgapn hgapm hterminal F G hF hG hFM hGM

end NLS.KdV
