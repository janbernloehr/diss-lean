import NLS.KdV.HillOddKernelFiniteGapContours

/-! # Actual linear and fifth-power intrinsic frequency periods -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The actual linear intrinsic period is fixed by the own zeroth period. -/
theorem hillIntrinsicLinearFrequency_gap_contribution
    (n : ℕ) (hn : 1≤n) (k : ℕ) (hk : 1≤k) :
    (∮ E in C((hillRealGapCenter q hq hr k : ℂ),hillIntrinsicGapRadius q hq hr k),
      hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E*
        hillAbelianSelectedGlobalPsi q hq hr n hn E/hillEnergyCanonicalRootProduct q hq hr E)=
      -2*I*(k:ℂ)*(Real.pi:ℂ)^2*(if k=n then 1 else 0) := by
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
  have hshift : (∮ E in C(c,r), (F E-s)*G E)=-s*frequencyMoment F G c r 0 := by
    have he := shifted_frequency_period F G c s r hrp.le hF hG 1
    simpa [Finset.sum_range_succ,h1] using he
  have hraw : (fun E => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E*
      hillAbelianSelectedGlobalPsi q hq hr n hn E/hillEnergyCanonicalRootProduct q hq hr E)=
        (fun E => (F E-s)*G E) := by
    funext E
    dsimp only [F,G,s,hillL2ShiftedPrimitive]
    ring
  rw [hillIntrinsicGapRadius,hraw,hshift]
  change -s*hillIntrinsicFrequencyMoment q hq hr n hn k 0=_
  rw [hillIntrinsicFrequencyMoment_zero q hq hr n hn k hk]
  dsimp only [s]
  ring

/-- The actual fifth intrinsic period has the source coefficients80
and-160*pi^2, with the selected leading fifth power retained. -/
theorem hillIntrinsicFifthFrequency_gap_contribution
    (n : ℕ) (hn : 1≤n) (k : ℕ) (hk : 1≤k) :
    (-16/(I*Real.pi) : ℂ)*(∮ E in C((hillRealGapCenter q hq hr k : ℂ),hillIntrinsicGapRadius q hq hr k),
      hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E^5*
        hillAbelianSelectedGlobalPsi q hq hr n hn E/hillEnergyCanonicalRootProduct q hq hr E)=
      80*(k:ℂ)*hillIntrinsicFrequencyMoment q hq hr n hn k 4-
        160*(Real.pi:ℂ)^2*(k:ℂ)^3*hillIntrinsicFrequencyMoment q hq hr n hn k 2+
        (if k=n then (2*(k:ℂ)*Real.pi)^5 else 0) := by
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
  have h5 : frequencyMoment F G c r 5=0 := by
    simpa only [hillIntrinsicFrequencyMoment] using hillIntrinsicFrequencyMoment_odd_eq_zero q hq hr n hn k hk 2
  have hshift : (∮ E in C(c,r), (F E-s)^5*G E)=
      -5*s*frequencyMoment F G c r 4-10*s^3*frequencyMoment F G c r 2-s^5*frequencyMoment F G c r 0 := by
    rw [shifted_frequency_period F G c s r hrp.le hF hG 5]
    norm_num [Finset.sum_range_succ,h1,h3,h5,show Nat.choose 5 2=10 by decide,show Nat.choose 5 3=10 by decide]
    ring
  have hraw : (fun E => hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E^5*
      hillAbelianSelectedGlobalPsi q hq hr n hn E/hillEnergyCanonicalRootProduct q hq hr E)=
        (fun E => (F E-s)^5*G E) := by
    funext E
    dsimp only [F,G,s,hillL2ShiftedPrimitive]
    ring
  have hp : (Real.pi:ℂ)≠0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  calc
    _ = 80*(k:ℂ)*frequencyMoment F G c r 4-
        160*(Real.pi:ℂ)^2*(k:ℂ)^3*frequencyMoment F G c r 2+
        16*(Real.pi:ℂ)^4*(k:ℂ)^5*frequencyMoment F G c r 0 := by
      rw [hillIntrinsicGapRadius,hraw,hshift]
      dsimp only [s]
      field_simp
      simp only [I_sq]
      ring_nf
      simp only [I_pow_four,mul_one]
    _ = _ := by
      change 80*(k:ℂ)*hillIntrinsicFrequencyMoment q hq hr n hn k 4-
        160*(Real.pi:ℂ)^2*(k:ℂ)^3*hillIntrinsicFrequencyMoment q hq hr n hn k 2+
        16*(Real.pi:ℂ)^4*(k:ℂ)^5*hillIntrinsicFrequencyMoment q hq hr n hn k 0=_
      rw [hillIntrinsicFrequencyMoment_zero q hq hr n hn k hk]
      split_ifs <;> ring


/-- The actual finite-gap linear period fixes the selected normalization. -/
theorem exists_hillFiniteGap_linear_period
    (n N : ℕ) (hn : 1≤n) (hnN : n≤N)
    (hclosed : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q hq hr k=0) :
    ∃ R : ℝ, 0<R ∧ ∀ S : ℝ, R<S →
      (∮ E in C(0,S), hillL2OddKernel q 0 (hillAbelianSelectedGlobalPsi q hq hr n hn) E)=
        -2*I*(n:ℂ)*(Real.pi:ℂ)^2 := by
  obtain ⟨R,hR,hcontour⟩ := exists_hillFiniteGap_odd_contour_decomposition q hq hr 0 n N hn hnN hclosed
  refine ⟨R,hR,?_⟩
  intro S hS
  rw [hcontour S hS]
  have he : (∑ k∈Finset.Icc 1 N, ∮ E in C((hillRealGapCenter q hq hr k : ℂ),hillIntrinsicGapRadius q hq hr k),
      hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E^(2*0+1)*
        hillAbelianSelectedGlobalPsi q hq hr n hn E/hillEnergyCanonicalRootProduct q hq hr E)=
      ∑ k∈Finset.Icc 1 N, (if k=n then -2*I*(n:ℂ)*(Real.pi:ℂ)^2 else 0) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Nat.mul_zero,zero_add,pow_one]
    rw [hillIntrinsicLinearFrequency_gap_contribution q hq hr n hn k (Finset.mem_Icc.mp hk).1]
    split_ifs with hkn
    · subst k
      ring
    · ring
  rw [he]
  simp only [Finset.sum_ite_eq',Finset.mem_Icc.mpr ⟨hn,hnN⟩,if_true]

/-- The actual fifth outer contour has the source leading fifth power
and exact fourth/second-moment coefficients, before physical mass renormalization. -/
theorem exists_hillFiniteGap_fifth_frequency_moments
    (n N : ℕ) (hn : 1≤n) (hnN : n≤N)
    (hclosed : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q hq hr k=0) :
    ∃ R : ℝ, 0<R ∧ ∀ S : ℝ, R<S →
      (-16/(I*Real.pi) : ℂ)*(∮ E in C(0,S), hillL2OddKernel q 2 (hillAbelianSelectedGlobalPsi q hq hr n hn) E)-
        (2*(n:ℂ)*Real.pi)^5=
        -160*(Real.pi:ℂ)^2*(∑ k∈Finset.Icc 1 N, (k:ℂ)^3*hillIntrinsicFrequencyMoment q hq hr n hn k 2)+
          80*(∑ k∈Finset.Icc 1 N, (k:ℂ)*hillIntrinsicFrequencyMoment q hq hr n hn k 4) := by
  obtain ⟨R,hR,hcontour⟩ := exists_hillFiniteGap_odd_contour_decomposition q hq hr 2 n N hn hnN hclosed
  refine ⟨R,hR,?_⟩
  intro S hS
  rw [hcontour S hS,Finset.mul_sum]
  have hsum : (∑ k∈Finset.Icc 1 N, (-16/(I*Real.pi) : ℂ)*
      (∮ E in C((hillRealGapCenter q hq hr k : ℂ),hillIntrinsicGapRadius q hq hr k),
        hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) E^(2*2+1)*
          hillAbelianSelectedGlobalPsi q hq hr n hn E/hillEnergyCanonicalRootProduct q hq hr E))=
      ∑ k∈Finset.Icc 1 N, (80*(k:ℂ)*hillIntrinsicFrequencyMoment q hq hr n hn k 4-
        160*(Real.pi:ℂ)^2*(k:ℂ)^3*hillIntrinsicFrequencyMoment q hq hr n hn k 2+
        if k=n then (2*(n:ℂ)*Real.pi)^5 else 0) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hillIntrinsicFifthFrequency_gap_contribution q hq hr n hn k (Finset.mem_Icc.mp hk).1]
    split_ifs with he
    · subst k
      rfl
    · rfl
  rw [hsum,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_Icc.mpr ⟨hn,hnN⟩,if_true]
  simp only [Finset.mul_sum,neg_mul,Finset.sum_neg_distrib,mul_assoc]
  ring

end NLS.KdV
