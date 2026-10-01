import NLS.ComplexAnalysis.QuadraticCauchyStationarity
import NLS.ZakharovShabat.SourceAngularEtaCauchyEquation
import NLS.ZakharovShabat.SourceAngularIntegrandIsospectral

/-! # Stationarity of the actual interior eta remainder

The diagonal remainder has the actual quadratic equation with right-hand
side equal to the actual normalized gap numerator minus `i`. Its variation
therefore satisfies the homogeneous equation, just as for off-diagonal beta.
Analytic uniqueness applies on the whole disc, including collapsed gaps.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex NLS.ComplexAnalysis NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourceAngularJointAnnulusChartData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {m : ℤ}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {W V : Set (CoeffPair p)} {c : ℤ → ℂ} {T : ℤ → ℝ} {r R : ℝ} {z₀ : ℂ}

/-- The actual eta remainder's interior candidate has zero variation
in every isospectral direction, throughout the disc and through collapse. -/
theorem fderiv_etaQuotientCauchyCandidate_isospectral_eq_zero
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ V) (hφ₀ : φ.val ∈ W₀)
    (h : CoeffPair p) (hiso : SourceIsospectralDirection hp φ.val h)
    (z : ℂ) (hz : z ∈ ball (c m) ρ) :
    (fderiv ℂ (fun ψ : CoeffPair p => sourceAngularEtaQuotientCauchyCandidate
      hp hp1 m s (c m) r R z₀ ρ (z,ψ)) φ.val) h = 0 := by
  let H := sourceAngularEtaQuotientCauchyCandidate hp hp1 m s (c m) r R z₀ ρ
  let N : ℂ × CoeffPair p → ℂ := fun t => sourceAngularGapNumerator hp hp1 m m s t.2 t.1-I
  let M : CoeffPair p → ℂ := fun ψ => sourceStandardRootMidpoint hp hp1 ψ m
  let G : CoeffPair p → ℂ := fun ψ => (canonicalPeriodicGap hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ) m)^2
  obtain ⟨A,_,_,hAreal,hMG⟩ := exists_global_source_analytic_midpoint_squaredGap hp hp1
  have hM : DifferentiableAt ℂ M φ.val := (hMG φ.val (hAreal φ.property) m).1.differentiableAt
  have hG : DifferentiableAt ℂ G φ.val := (hMG φ.val (hAreal φ.property) m).2.differentiableAt
  have hMGzero : (fderiv ℂ M φ.val) h = 0 ∧ (fderiv ℂ G φ.val) h = 0 :=
    fderiv_canonicalPeriodicMidpoint_squaredGap_isospectral_eq_zero hp hp1 φ.val φ.property h hiso m
  let a := canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m
  let b := canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m
  have ha : a ∈ ball (c m) ρ :=
    ball_subset_ball hrρ.le (D.gap_enclosed φ.val hφ (left_mem_segment ℝ a b))
  apply fderiv_quadratic_equation_eq_zero_of_stationary_data H N M G (ball (c m) ρ) V
    isOpen_ball D.source_open (convex_ball (c m) ρ).isPreconnected φ.val h hφ a b ha
    rfl rfl hM hG hMGzero (D.analyticOnNhd_etaQuotientCauchyCandidate ρ hrρ hρR) _ _ z hz
  · intro ψ hψ w hw
    exact D.etaQuotientCauchyCandidate_equation ψ hψ ρ hrρ hρR w hw
  · intro w hw
    have hother : w ∈ sourceStandardRootOmittedDomain hp hp1 φ.val m :=
      ((D.disc_family φ.val hφ).contour_family.2 m).2.2.1
        (ball_subset_closedBall (ball_subset_ball (hρR.trans D.outer_lt_assigned).le hw))
    simpa only [N,fderiv_sub_const] using
      hs.fderiv_angularGapNumerator_isospectral_eq_zero m m φ hφ₀ h hiso w hother

/-- The fixed-parameter interior eta remainder commutes with every
actual action, including at either periodic endpoint and at closed gaps. -/
theorem sourceBracket_etaQuotientCauchyCandidate_action_eq_zero
    (D : SourceAngularJointAnnulusChartData hp hp1 m s W V c T r R z₀)
    {W₀ : Set (CoeffPair p)} (hs : SourcePsiIsolatingComplexExtension hp hp1 W₀ s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (k : ℤ)
    (ρ : ℝ) (hrρ : r < ρ) (hρR : ρ < R)
    (φ : realTypeSourceLocus p) (hφ : φ.val ∈ V) (hφ₀ : φ.val ∈ W₀)
    (z : ℂ) (hz : z ∈ ball (c m) ρ) :
    sourceBracket h2p (fun ψ : CoeffPair p => sourceAngularEtaQuotientCauchyCandidate
      hp hp1 m s (c m) r R z₀ ρ (z,ψ)) (sourceComplexAction hp hp1 k) φ.val = 0 := by
  rw [← fderiv_apply_sourceHamiltonianVector]
  exact D.fderiv_etaQuotientCauchyCandidate_isospectral_eq_zero hs ρ hrρ hρR φ hφ hφ₀ _
    (sourceHamiltonianVector_action_isospectral hp hp1 h2p φ.val φ.property k) z hz

end SourceAngularJointAnnulusChartData
end NLS.ZakharovShabat
