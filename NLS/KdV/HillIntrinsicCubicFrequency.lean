import NLS.KdV.HillIntrinsicFrequencyMoments

/-! # Actual intrinsic cubic frequency contributions and finite sums -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The literal actual cubic contour on each intrinsic gap has the source
coefficient -12*k and the exact own-mode leading contribution. -/
theorem hillIntrinsicCubicFrequency_gap_contribution
    (n : ℕ) (hn : 1≤n) (k : ℕ) (hk : 1≤k) :
    (4/(I*Real.pi) : ℂ)*(∮ E in C((hillRealGapCenter q hq hr k : ℂ),
      hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k),
      hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E^3*
        hillAbelianSelectedGlobalPsi q hq hr n hn E/hillEnergyCanonicalRootProduct q hq hr E)=
      -12*(k:ℂ)*hillIntrinsicFrequencyMoment q hq hr n hn k 2+
        (if k=n then (2*(k:ℂ)*Real.pi)^3 else 0) := by
  let c : ℂ := hillRealGapCenter q hq hr k
  let r := hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k
  let F := hillL2ShiftedPrimitive q k
  let G := fun E => hillAbelianSelectedGlobalPsi q hq hr n hn E/hillEnergyCanonicalRootProduct q hq hr E
  let s : ℂ := I*(k:ℂ)*Real.pi
  obtain ⟨hd,hη,_⟩ := hillRealGapContour_geometry q hq hr k hk
  have hrp : 0<r := add_pos_of_nonneg_of_pos hd hη
  have hcut := hillRealGapContour_sphere_subset q hq hr k hk
  have hF : ContinuousOn F (sphere c r) :=
    ((analyticOnNhd_hillL2RealCutPrimitive q hq hr).continuousOn.mono hcut).add continuousOn_const
  have hG : ContinuousOn G (sphere c r) := by
    intro E hE
    exact ((analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn E (mem_univ _)).div
      (analyticOnNhd_hillEnergyCanonicalRootProduct q hq hr E (hcut hE))
      (by rw [hillEnergyCanonicalRootProduct_eq_realCutRoot q hq hr (hcut hE)];
          exact hillL2RealCutRoot_ne_zero q hq hr E (hcut hE))).continuousAt.continuousWithinAt
  have h1 : frequencyMoment F G c r 1=0 := by
    simpa only [hillIntrinsicFrequencyMoment,Nat.mul_zero,zero_add] using
      hillIntrinsicFrequencyMoment_odd_eq_zero q hq hr n hn k hk 0
  have h3 : frequencyMoment F G c r 3=0 := by
    simpa only [hillIntrinsicFrequencyMoment] using hillIntrinsicFrequencyMoment_odd_eq_zero q hq hr n hn k hk 1
  have hshift : (∮ E in C(c,r), (F E-s)^3*G E)=
      -3*s*frequencyMoment F G c r 2-s^3*frequencyMoment F G c r 0 := by
    rw [shifted_frequency_period F G c s r hrp.le hF hG 3]
    norm_num [Finset.sum_range_succ,h1,h3]
    ring
  have hraw : (fun E => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E^3*
      hillAbelianSelectedGlobalPsi q hq hr n hn E/hillEnergyCanonicalRootProduct q hq hr E)=
        (fun E => (F E-s)^3*G E) := by
    funext E
    dsimp only [F,G,s,hillL2ShiftedPrimitive]
    ring
  have hp : (Real.pi:ℂ)≠0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  calc
    _ = -12*(k:ℂ)*frequencyMoment F G c r 2+
        4*(k:ℂ)^3*(Real.pi:ℂ)^2*frequencyMoment F G c r 0 := by
      rw [hraw,hshift]
      dsimp only [s]
      field_simp
      simp only [I_sq]
      ring
    _ = _ := by
      change -12*(k:ℂ)*hillIntrinsicFrequencyMoment q hq hr n hn k 2+
        4*(k:ℂ)^3*(Real.pi:ℂ)^2*hillIntrinsicFrequencyMoment q hq hr n hn k 0=_
      rw [hillIntrinsicFrequencyMoment_zero q hq hr n hn k hk]
      split_ifs <;> ring

end NLS.KdV
