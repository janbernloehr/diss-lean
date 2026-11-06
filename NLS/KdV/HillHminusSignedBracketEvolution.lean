import NLS.KdV.HillHminusConjugateActionRotation
import NLS.KdV.HillHminusSignedCartesianGardnerLimits
import NLS.Poisson.HminusGardnerWeightedEvolution

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

/-- The actual complex rotation weights for the two ORIGINAL Cartesian signs. -/
def hillCartesianActionRotationWeight (σ : Bool) (n k : ℕ+) : ℂ :=
  (if σ then I else -I) * (if (k:ℕ)=(n:ℕ) then 1 else 0)

theorem hillSignedCartesian_action_hminus_Gardner_eq
    (q : RealPeriodOneHillPotential) (n k : ℕ+) (σ : Bool)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (F J : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hJ : AnalyticAt ℂ J (hillOriginalHminusSource q.val))
    (hFM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p)
    (hJM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      J (hillOriginalHminusSource p.val) = (hillRealGapIntegral p.val p.property.1 p.property.2 k 0 : ℂ)) :
    NLS.Poisson.hminusGardnerBracket F J (hillOriginalHminusSource q.val) =
      hillCartesianActionRotationWeight σ n k * F (hillOriginalHminusSource q.val) := by
  rw [hFM.self_of_nhds]
  cases σ
  · exact hillOriginalConjugateCartesian_action_hminus_Gardner_eq q n k hgap F J hF hJ hFM hJM
  · exact hillOriginalCartesian_action_hminus_Gardner_eq q n k F J hF hJ hFM hJM

theorem hillSignedCartesian_action_hminus_Gardner_fderiv
    (q : RealPeriodOneHillPotential) (n k : ℕ+) (σ : Bool)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (F J : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hJ : AnalyticAt ℂ J (hillOriginalHminusSource q.val))
    (hFM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p)
    (hJM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      J (hillOriginalHminusSource p.val) = (hillRealGapIntegral p.val p.property.1 p.property.2 k 0 : ℂ)) :
    fderiv ℂ (NLS.Poisson.hminusGardnerBracket F J) (hillOriginalHminusSource q.val) =
      hillCartesianActionRotationWeight σ n k • fderiv ℂ F (hillOriginalHminusSource q.val) := by
  cases σ
  · exact hillOriginalConjugateCartesian_action_hminus_Gardner_fderiv q n k hgap F J hF hJ hFM hJM
  · exact hillOriginalCartesian_action_hminus_Gardner_fderiv q n k F J hF hJ hFM hJM

/-- The actual evolution law for ALL FOUR Cartesian Gardner entries
under every genuine ORIGINAL action Hamiltonian, with exact signed weights. -/
theorem hillSignedCartesian_bracket_action_hminus_evolution
    (q : RealPeriodOneHillPotential) (n m k : ℕ+) (σ τ : Bool)
    (hgapn : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (hgapm : hillRealGapHalfLength q.val q.property.1 q.property.2 m ≠ 0)
    (F G J : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hG : AnalyticAt ℂ G (hillOriginalHminusSource q.val))
    (hJ : AnalyticAt ℂ J (hillOriginalHminusSource q.val))
    (hFM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p)
    (hGM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian τ m p)
    (hJM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      J (hillOriginalHminusSource p.val) = (hillRealGapIntegral p.val p.property.1 p.property.2 k 0 : ℂ)) :
    (fderiv ℂ (NLS.Poisson.hminusGardnerBracket F G) (hillOriginalHminusSource q.val))
        (NLS.Poisson.gardnerHamiltonianVector J (hillOriginalHminusSource q.val)) =
      (hillCartesianActionRotationWeight σ n k + hillCartesianActionRotationWeight τ m k) *
        NLS.Poisson.hminusGardnerBracket F G (hillOriginalHminusSource q.val) := by
  exact NLS.Poisson.hminusGardnerBracket_weighted_hamiltonian_derivative F G J _ _ _ hF hG hJ
    (hillSignedCartesian_action_hminus_Gardner_fderiv q n k σ hgapn F J hF hJ hFM hJM)
    (hillSignedCartesian_action_hminus_Gardner_fderiv q m k τ hgapm G J hG hJ hGM hJM)

end NLS.KdV
