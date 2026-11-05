import NLS.KdV.HillHminusSignedBracketEvolution
import NLS.Poisson.HminusGardnerNormalizedEvolution

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
namespace NLS.KdV

theorem hillSignedSpectralCartesian_ne_zero_open
    (q : RealPeriodOneHillPotential) (n : ℕ+) (σ : Bool)
    (hgap : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0) :
    hillSignedSpectralCartesian σ n q ≠ 0 := by
  have h := hillSpectralCartesian_ne_zero_open q n hgap
  cases σ <;> simpa [hillSignedSpectralCartesian] using h

/-- ALL FOUR ORIGINAL signed Cartesian Gardner brackets, normalized by
their actual nonzero physical coordinates, are stationary under EVERY
actual action Hamiltonian. The genuine physical negative source direction
has the same stationary normalized value. -/
theorem hillSignedCartesian_normalized_bracket_action_stationary
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
    (fderiv ℂ (fun a => NLS.Poisson.hminusGardnerBracket F G a / (F a * G a))
        (hillOriginalHminusSource q.val))
        (NLS.Poisson.gardnerHamiltonianVector J (hillOriginalHminusSource q.val)) = 0 ∧
      (fderiv ℂ (fun a => NLS.Poisson.hminusGardnerBracket F G a / (F a * G a))
        (hillOriginalHminusSource q.val))
        (hillOriginalHminusSource (hillPhysicalMomentHamiltonianSource
          q.val q.property.1 q.property.2 k k.pos 0)) = 0 := by
  have hFn : F (hillOriginalHminusSource q.val) ≠ 0 := by
    rw [hFM.self_of_nhds]
    exact hillSignedSpectralCartesian_ne_zero_open q n σ hgapn
  have hGn : G (hillOriginalHminusSource q.val) ≠ 0 := by
    rw [hGM.self_of_nhds]
    exact hillSignedSpectralCartesian_ne_zero_open q m τ hgapm
  have he := NLS.Poisson.hminusGardnerBracket_normalized_hamiltonian_derivative_zero F G J _ _ _
    hF hG hJ hFn hGn
    (hillSignedCartesian_action_hminus_Gardner_eq q n k σ hgapn F J hF hJ hFM hJM)
    (hillSignedCartesian_action_hminus_Gardner_eq q m k τ hgapm G J hG hJ hGM hJM)
    (hillSignedCartesian_action_hminus_Gardner_fderiv q n k σ hgapn F J hF hJ hFM hJM)
    (hillSignedCartesian_action_hminus_Gardner_fderiv q m k τ hgapm G J hG hJ hGM hJM)
  refine ⟨he,?_⟩
  rw [hillOriginalAction_hminus_HamiltonianVector_eq_neg_source q k J hJ hJM,map_neg] at he
  exact neg_eq_zero.mp he

end NLS.KdV
