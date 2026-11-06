import NLS.KdV.HillHminusActionTraceStationarity
import NLS.KdV.HillHminusNormalizedCartesianBrackets

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.Poisson
namespace NLS.KdV

/-- Every normalized ORIGINAL signed Cartesian bracket is stationary
under EVERY fixed-energy true trace Hamiltonian and its actual physical
source. All four signs and all positive indices are included. -/
theorem hillSignedCartesian_normalized_bracket_trace_stationary
    (q : RealPeriodOneHillPotential) (n m : ℕ+) (σ τ : Bool)
    (hgapn : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (hgapm : hillRealGapHalfLength q.val q.property.1 q.property.2 m ≠ 0)
    (F G : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hG : AnalyticAt ℂ G (hillOriginalHminusSource q.val))
    (hFM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p)
    (hGM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian τ m p) (E : ℂ) :
    (fderiv ℂ (fun a => hminusGardnerBracket F G a/(F a*G a)) (hillOriginalHminusSource q.val))
      (gardnerHamiltonianVector (fun a => hillHminusDiscriminant a E) (hillOriginalHminusSource q.val)) = 0 ∧
      (fderiv ℂ (fun a => hminusGardnerBracket F G a/(F a*G a)) (hillOriginalHminusSource q.val))
        (hillOriginalHminusSource (hillEnergyHamiltonianSource (SpectralWeight.one.toCoeff q.val) E)) = 0 := by
  let D : PeriodOneHminusOne → ℂ := fun a => hminusGardnerBracket F G a/(F a*G a)
  have hkernel (k : ℕ+) : (fderiv ℂ D (hillOriginalHminusSource q.val))
      (hillOriginalHminusSource (hillPhysicalMomentHamiltonianSource q.val q.property.1 q.property.2 k k.pos 0)) = 0 := by
    obtain ⟨J,hJ,hJM⟩ := exists_hillOriginal_action_hminus_physical_germ q k
    exact (hillSignedCartesian_normalized_bracket_action_stationary q n m k σ τ hgapn hgapm
      F G J hF hG hJ hFM hGM hJM).2
  have ht := hillHminus_trace_stationary_of_all_action_sources q D hkernel E
  exact ⟨by rw [fderiv_apply_gardnerHamiltonianVector]; exact ht.1,ht.2⟩

/-- The trace energy is frozen at THIS basepoint's actual Dirichlet
label. This proves the genuine normalized indexed-source stationarity
without differentiating a moving-energy Hamiltonian. -/
theorem hillSignedCartesian_normalized_bracket_indexed_stationary
    (q : RealPeriodOneHillPotential) (n m k : ℕ+) (σ τ : Bool)
    (hgapn : hillRealGapHalfLength q.val q.property.1 q.property.2 n ≠ 0)
    (hgapm : hillRealGapHalfLength q.val q.property.1 q.property.2 m ≠ 0)
    (F G : PeriodOneHminusOne → ℂ)
    (hF : AnalyticAt ℂ F (hillOriginalHminusSource q.val))
    (hG : AnalyticAt ℂ G (hillOriginalHminusSource q.val))
    (hFM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian σ n p)
    (hGM : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      G (hillOriginalHminusSource p.val) = hillSignedSpectralCartesian τ m p) :
    (fderiv ℂ (fun a => hminusGardnerBracket F G a/(F a*G a)) (hillOriginalHminusSource q.val))
      (hillOriginalHminusSource (hillIndexedDiscriminantHamiltonianSource q k k.pos)) = 0 :=
  (hillSignedCartesian_normalized_bracket_trace_stationary q n m σ τ hgapn hgapm
    F G hF hG hFM hGM (hillDirichletEnergy q.val q.property.1 q.property.2 k k.pos)).2

end NLS.KdV
