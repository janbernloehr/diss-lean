import NLS.ComplexAnalysis.SquaredCircleBandHomotopy
import NLS.KdV.HillGlobalNormalizedDifferentials
import NLS.KdV.HillRealGapContourDiscs

/-! # Independent normalized Hill periods on squared frequency circles

Any positive-frequency circle whose squared real crossings lie in the
two indexed open bands has the same energy period as the intrinsic Hill
circle, including a collapsed indexed gap.
-/
noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV

theorem hillTwoBands_subset_realCutDomain
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (j : ℕ) (hj : 1 ≤ j)
    (z : ℂ) (hz : z.im ≠ 0 ∨
      z.re ∈ Ioo (hillRealLabels q hq hr (2*j-2)) (hillRealLabels q hq hr (2*j-1)) ∨
      z.re ∈ Ioo (hillRealLabels q hq hr (2*j)) (hillRealLabels q hq hr (2*j+1))) :
    z ∈ hillL2RealCutDomain q hq hr := by
  rcases hz with hi | hlo | hup
  · exact Or.inl hi
  · apply Or.inr
    refine ⟨j-1,?_⟩
    simpa only [show 2*(j-1) = 2*j-2 by omega,show 2*j-2+1 = 2*j-1 by omega] using hlo
  · exact Or.inr ⟨j,hup⟩

theorem hillIntrinsicCircle_band_crossings
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (j : ℕ) (hj : 1 ≤ j) :
    let d := hillRealGapCenter q hq hr j
    let R := hillRealGapHalfLength q hq hr j+hillRealGapCollar q hq hr j
    0 < R ∧ d-R ∈ Ioo (hillRealLabels q hq hr (2*j-2)) (hillRealLabels q hq hr (2*j-1)) ∧
      d+R ∈ Ioo (hillRealLabels q hq hr (2*j)) (hillRealLabels q hq hr (2*j+1)) := by
  have hg := hillRealGapContour_geometry q hq hr j hj
  have hb := hillRealGapContour_band_bounds q hq hr j hj
  dsimp only
  refine ⟨by linarith only [hg.1,hg.2.1],⟨hb.1,?_⟩,⟨?_,hb.2⟩⟩
  · linarith only [hg.2.2.1,hg.2.1]
  · linarith only [hg.2.2.2.1,hg.2.1]

theorem analyticOnNhd_hillEntireNumerator_div_root
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℂ → ℂ) (hN : AnalyticOnNhd ℂ N univ) :
    AnalyticOnNhd ℂ (fun E => N E/hillEnergyCanonicalRootProduct q hq hr E)
      (hillL2RealCutDomain q hq hr) := by
  intro E hE
  exact (hN E (mem_univ _)).div (analyticOnNhd_hillEnergyCanonicalRootProduct q hq hr E hE)
    (hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain q hq hr E hE)

theorem hillSquaredCircle_period_eq_intrinsic
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (j : ℕ) (hj : 1 ≤ j)
    (c r : ℝ) (hr0 : 0 < r) (hrc : r < c)
    (hl : (c-r)^2 ∈ Ioo (hillRealLabels q hq hr (2*j-2)) (hillRealLabels q hq hr (2*j-1)))
    (hu : (c+r)^2 ∈ Ioo (hillRealLabels q hq hr (2*j)) (hillRealLabels q hq hr (2*j+1)))
    (N : ℂ → ℂ) (hN : AnalyticOnNhd ℂ N univ) :
    (∮ z in C((c:ℂ),r),2*z*(N (z^2)/hillEnergyCanonicalRootProduct q hq hr (z^2))) =
      ∮ E in C((hillRealGapCenter q hq hr j : ℂ),
        hillRealGapHalfLength q hq hr j+hillRealGapCollar q hq hr j),
        N E/hillEnergyCanonicalRootProduct q hq hr E := by
  obtain ⟨hR,hleft,hright⟩ := hillIntrinsicCircle_band_crossings q hq hr j hj
  exact circleIntegral_square_eq_of_real_bands
    (fun E => N E/hillEnergyCanonicalRootProduct q hq hr E) (hillL2RealCutDomain q hq hr) c r
    (hillRealGapCenter q hq hr j) (hillRealGapHalfLength q hq hr j+hillRealGapCollar q hq hr j)
    (hillRealLabels q hq hr (2*j-2)) (hillRealLabels q hq hr (2*j-1))
    (hillRealLabels q hq hr (2*j)) (hillRealLabels q hq hr (2*j+1))
    hr0 hrc hR hl hleft hu hright (hillTwoBands_subset_realCutDomain q hq hr j hj)
    (analyticOnNhd_hillEntireNumerator_div_root q hq hr N hN)

theorem hillSelectedPsi_squared_circle_period
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (j : ℕ) (hj : 1 ≤ j)
    (c r : ℝ) (hr0 : 0 < r) (hrc : r < c)
    (hl : (c-r)^2 ∈ Ioo (hillRealLabels q hq hr (2*j-2)) (hillRealLabels q hq hr (2*j-1)))
    (hu : (c+r)^2 ∈ Ioo (hillRealLabels q hq hr (2*j)) (hillRealLabels q hq hr (2*j+1)))
    (n : ℕ) (hn : 1 ≤ n) :
    (∮ z in C((c:ℂ),r),z*hillAbelianSelectedGlobalPsi q hq hr n hn (z^2)/
      hillEnergyCanonicalRootProduct q hq hr (z^2)) = (Real.pi:ℂ)*(if j = n then 1 else 0) := by
  have he := hillSquaredCircle_period_eq_intrinsic q hq hr j hj c r hr0 hrc hl hu
    (hillAbelianSelectedGlobalPsi q hq hr n hn) (analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn)
  have hp := hillAbelianSelectedGlobalPsi_intrinsic_periods q hq hr n hn j hj
  have hh : (∮ z in C((c:ℂ),r),2*z*(hillAbelianSelectedGlobalPsi q hq hr n hn (z^2)/
      hillEnergyCanonicalRootProduct q hq hr (z^2))) =
      2*(∮ z in C((c:ℂ),r),z*hillAbelianSelectedGlobalPsi q hq hr n hn (z^2)/
        hillEnergyCanonicalRootProduct q hq hr (z^2)) := by
    rw [← circleIntegral.integral_const_mul]
    congr 1
    funext z
    ring
  rw [hh] at he
  rw [← he] at hp
  have hπ : (Real.pi:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp at hp
  exact hp

end NLS.KdV
