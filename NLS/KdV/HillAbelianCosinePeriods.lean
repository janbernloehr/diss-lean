import NLS.KdV.HillCollapsedAngularDifferential
import NLS.KdV.HillAbelianCosinePrimitive
import NLS.KdV.HillGlobalGapPeriodCriterion
import NLS.ComplexAnalysis.EndpointRootCosinePeriod

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat MeasureTheory
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem integral_hillAbelianCosineDifferential (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) :
    (∫ θ in (0 : ℝ)..Real.pi, hillAbelianCosineDifferential q hq hr n hn k (θ : ℂ)) =
      (Real.pi : ℂ)*(if k = n then 1 else 0) := by
  by_cases hc : hillRealLabels q hq hr (2*k-1) = hillRealLabels q hq hr (2*k)
  · simp_rw [hillAbelianCosineDifferential_of_closed_gap q hq hr n hn k hk hc]
    rw [intervalIntegral.integral_const,sub_zero,Complex.real_smul]
  let τ : ℂ := hillRealGapCenter q hq hr k
  let δ : ℂ := hillRealGapHalfLength q hq hr k
  let r := hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k
  let U := hillDeflatedEnergyCanonicalRoot q hq hr k
  let N := hillAbelianSelectedGlobalPsi q hq hr n hn
  let g : ℂ → ℂ := fun E => N E/U E
  have hgeom := hillRealGapContour_geometry q hq hr k hk
  have hd : 0 < hillRealGapHalfLength q hq hr k := by
    have hab := lt_of_le_of_ne (monotone_hillRealLabels q hq hr (by omega : 2*k-1 ≤ 2*k)) hc
    dsimp only [hillRealGapHalfLength]
    linarith
  have hδ : δ ≠ 0 := by dsimp only [δ];exact ofReal_ne_zero.mpr hd.ne'
  have hdr : ‖δ‖ < r := by
    rw [show ‖δ‖ = hillRealGapHalfLength q hq hr k by dsimp only [δ];rw [norm_real,Real.norm_eq_abs,abs_of_pos hd]]
    dsimp only [r]
    linarith [hgeom.2.1]
  obtain ⟨R,hrR,hRdisc⟩ := exists_hillIntrinsicContour_enlarged_disc_in_filledDomain q hq hr k hk
  have hg : AnalyticOnNhd ℂ g (closedBall τ R) := by
    intro E hE
    exact (analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn E (mem_univ _)).div
      (analyticOnNhd_hillDeflatedEnergyCanonicalRoot q hq hr k E (hRdisc hE))
      (hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk E (hRdisc hE))
  have hl : τ-δ = (hillRealLabels q hq hr (2*k-1) : ℂ) := by
    dsimp only [τ,δ]
    rw [← ofReal_sub,hgeom.2.2.1]
  have hu : τ+δ = (hillRealLabels q hq hr (2*k) : ℂ) := by
    dsimp only [τ,δ]
    rw [← ofReal_add,hgeom.2.2.2.1]
  have heq : (fun E => N E/hillEnergyCanonicalRootProduct q hq hr E) =
      (fun E => g E/endpointRoot (τ-δ) (τ+δ) E) := by
    funext E
    rw [hl,hu,hillEnergyCanonicalRootProduct_eq_endpoint_mul_deflated q hq hr k hk E]
    dsimp only [g,U]
    ring
  have hraw := circleIntegral_div_endpointRoot_eq_cosine_integral g τ δ r R hδ hdr hrR hg
  have hp := hillAbelianSelectedGlobalPsi_intrinsic_periods q hq hr n hn k hk
  change (2*(Real.pi : ℂ))⁻¹*(∮ E in C(τ,r), N E/hillEnergyCanonicalRootProduct q hq hr E) = _ at hp
  rw [heq,hraw] at hp
  have hD : (∫ θ in (0 : ℝ)..Real.pi, hillAbelianCosineDifferential q hq hr n hn k (θ : ℂ)) =
      -I*(∫ θ in (0 : ℝ)..Real.pi, g (cosineGapPoint τ δ (θ : ℂ))) := by
    exact intervalIntegral.integral_const_mul _ _
  rw [hD,← hp]
  field_simp

end NLS.KdV
