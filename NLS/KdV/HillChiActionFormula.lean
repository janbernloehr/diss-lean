import NLS.KdV.HillOmittedEnergyCriticalProduct
import NLS.KdV.HillL2BoundaryGapProfile
import NLS.KdV.HillL2AllBoundaryLimits
import NLS.ComplexAnalysis.RealEndpointRootBoundary
import NLS.ComplexAnalysis.RealGapDiscIsolation
import NLS.ComplexAnalysis.RealGapArcsineIntegral

/-! # The exact real Hill action formula and its reduction to a chi bound. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat NLS.ComplexAnalysis
open MeasureTheory intervalIntegral
namespace NLS.KdV

theorem tendsto_hillL2LogDifferential_upper_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Ioo (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n))) :
    Tendsto (fun z => deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
      hillEnergyCanonicalRootProduct q hq hr z) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 ((((hillGapCriticalPoint q hq hr n-x)/
        (2*Real.sqrt ((x-hillRealLabels q hq hr (2*n-1))*(hillRealLabels q hq hr (2*n)-x))) : ℝ) : ℂ)*
        hillEnergyChi q hq hr n x)) := by
  let a := hillRealLabels q hq hr (2*n-1)
  let b := hillRealLabels q hq hr (2*n)
  let c := hillGapCriticalPoint q hq hr n
  let s := Real.sqrt ((x-a)*(b-x))
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2))
  have hsne : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hfilled := hillGapSegment_subset_filledDomain q hq hr n hn
    (ofReal_mem_ordered_segment _ _ x (monotone_hillRealLabels q hq hr (by omega : 2*n-1 ≤ 2*n)) (Ioo_subset_Icc_self hx))
  have hE := (endpointRoot_real_gap_limits a b x (hx.1.trans hx.2) (Ioo_subset_Icc_self hx)).1
  have hN : Tendsto (fun z : ℂ => (c : ℂ)-z) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 ((c : ℂ)-x)) :=
    (continuous_const.sub continuous_id).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hChi := ((analyticOnNhd_hillEnergyChi q hq hr n) x hfilled).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[{z : ℂ | 0 < z.im}] (x : ℂ) ≤ 𝓝 (x : ℂ))
  have h := ((hN.div hE (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hsne)).div_const (2*I)).mul hChi
  have hv : (((c : ℂ)-x)/(-I*(s : ℂ)))/(2*I)*hillEnergyChi q hq hr n x =
      (((c-x)/(2*s) : ℝ) : ℂ)*hillEnergyChi q hq hr n x := by
    push_cast
    field_simp [hsne]
    simp only [I_sq]
    ring
  change Tendsto (fun z => hillEnergyCriticalRootRatio q hq hr n z/(2*I)*hillEnergyChi q hq hr n z)
    (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 ((((c : ℂ)-x)/(-I*(s : ℂ)))/(2*I)*hillEnergyChi q hq hr n x)) at h
  rw [hv] at h
  apply h.congr'
  have hfilled_event : ∀ᶠ z in 𝓝[{z : ℂ | 0 < z.im}] (x : ℂ), z ∈ hillGapFilledDomain q hq hr n :=
    nhdsWithin_le_nhds ((isOpen_hillGapFilledDomain q hq hr n).mem_nhds hfilled)
  filter_upwards [hfilled_event,self_mem_nhdsWithin] with z hz hu
  exact (hillL2LogarithmicDifferential_selectedFactor q hq hr n hn z (Or.inl (ne_of_gt hu)) hz).symm

theorem hasDerivAt_hillRealGapProfile_chi
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (x : ℝ)
    (hx : x ∈ Ioo (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n))) :
    HasDerivAt (hillRealGapProfile (SpectralWeight.one.toCoeff q) n)
      ((hillGapCriticalPoint q hq hr n-x)/
        (2*Real.sqrt ((x-hillRealLabels q hq hr (2*n-1))*(hillRealLabels q hq hr (2*n)-x)))*
        (hillEnergyChi q hq hr n x).re) x := by
  let := real_upper_nhds_neBot x
  have hreg := hillL2Radicand_ne_zero_between_labels q hq hr (2*n-1) x
    (by simpa only [show 2*n-1+1 = 2*n by omega] using hx)
  have hdata := hillL2UpperBoundary_data q hq hr x hreg
  have hD := ((analyticOnNhd_hillL2Discriminant (SpectralWeight.one.toCoeff q)).deriv x (mem_univ _)).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[{z : ℂ | 0 < z.im}] (x : ℂ) ≤ 𝓝 (x : ℂ))
  have hdiv := hD.div (tendsto_hillL2UpperBoundaryRoot_all q hq hr x) hdata.1
  have hsrc : Tendsto (fun z => deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
      hillEnergyCanonicalRootProduct q hq hr z) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ))
      (𝓝 (deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) x /
        hillL2UpperBoundaryRoot (SpectralWeight.one.toCoeff q) x)) := by
    apply hdiv.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    rw [hillEnergyCanonicalRootProduct_eq_realCutRoot q hq hr (Or.inl (ne_of_gt hz)),
      hillL2RealCutRoot_eq_source q hq hr z (ne_of_gt hz)]
    rfl
  have he := tendsto_nhds_unique hsrc (tendsto_hillL2LogDifferential_upper_gap q hq hr n hn x hx)
  have hd := hdata.2.2.1
  rw [he] at hd
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hd
  have heq : (fun y : ℝ => (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) y).re) =ᶠ[𝓝 x]
      hillRealGapProfile (SpectralWeight.one.toCoeff q) n := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact (hillL2UpperBoundaryPrimitive_gap_profile q hq hr n hn y hy).2.1
  have hreal := hre.congr_of_eventuallyEq heq.symm
  simpa only [Complex.reCLM_apply,mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero] using hreal


theorem hillRealGapIntegral_eq_chi_integral
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) :
    hillRealGapIntegral q hq hr n 0 = (1/Real.pi)*
      ∫ x in (hillRealLabels q hq hr (2*n-1))..(hillRealLabels q hq hr (2*n)),
        (hillGapCriticalPoint q hq hr n-x)^2*(hillEnergyChi q hq hr n x).re /
          Real.sqrt ((x-hillRealLabels q hq hr (2*n-1))*(hillRealLabels q hq hr (2*n)-x)) := by
  by_cases hclosed : hillRealLabels q hq hr (2*n-1) = hillRealLabels q hq hr (2*n)
  · simp only [hillRealGapIntegral,hclosed,intervalIntegral.integral_same,mul_zero]
  have hab : hillRealLabels q hq hr (2*n-1) < hillRealLabels q hq hr (2*n) :=
    lt_of_le_of_ne (monotone_hillRealLabels q hq hr (by omega : 2*n-1 ≤ 2*n)) hclosed
  let a := hillRealLabels q hq hr (2*n-1)
  let b := hillRealLabels q hq hr (2*n)
  let c := hillGapCriticalPoint q hq hr n
  let H : ℝ → ℝ := fun x => (hillEnergyChi q hq hr n x).re
  let f := hillRealGapProfile (SpectralWeight.one.toCoeff q) n
  let fp : ℝ → ℝ := fun x => (c-x)/(2*Real.sqrt ((x-a)*(b-x)))*H x
  have hfilled (y : ℝ) (hy : y ∈ Icc a b) : (y : ℂ) ∈ hillGapFilledDomain q hq hr n :=
    hillGapSegment_subset_filledDomain q hq hr n hn
      (ofReal_mem_ordered_segment _ _ y (monotone_hillRealLabels q hq hr (by omega : 2*n-1 ≤ 2*n)) hy)
  have hH : ContinuousOn H (Icc a b) := continuous_re.comp_continuousOn
    ((analyticOnNhd_hillEnergyChi q hq hr n).continuousOn.comp continuous_ofReal.continuousOn hfilled)
  have hweight : ContinuousOn (fun x => (c-x)*H x/2) (Icc a b) :=
    ((continuousOn_const.sub continuousOn_id).mul hH).div_const 2
  have hkernel := intervalIntegrable_gap_arcsine_kernel a b hab
  have hi : IntervalIntegrable (fun x => ((c-x)*H x/2)*(Real.sqrt ((x-a)*(b-x)))⁻¹) volume a b :=
    hkernel.continuousOn_mul (by rwa [uIcc_of_le hab.le])
  have hfp : IntervalIntegrable fp volume a b := by
    convert! hi using 1
    funext x
    dsimp only [fp]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hd (x : ℝ) (hx : x ∈ Ioo a b) : HasDerivAt f (fp x) x :=
    hasDerivAt_hillRealGapProfile_chi q hq hr n hn x hx
  obtain ⟨hfa,hfb⟩ := hillRealGapProfile_endpoints q hq hr n hn
  have he := integral_eq_weighted_deriv_of_zero_endpoints f fp a b c hab.le
    (continuousOn_hillRealGapProfile q hq hr n hn) hfa hfb hd hfp
  have halg : (fun x => (c-x)*fp x) = fun x => (1/2)*((c-x)^2*H x/Real.sqrt ((x-a)*(b-x))) := by
    funext x
    dsimp only [fp]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [halg,intervalIntegral.integral_const_mul] at he
  change (2/Real.pi)*(∫ x in a..b, x^0*f x) = (1/Real.pi)*∫ x in a..b, (c-x)^2*H x/Real.sqrt ((x-a)*(b-x))
  simp only [pow_zero,one_mul]
  rw [he]
  ring


theorem hillRealGapIntegral_le_chi_bound
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x ∈ Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)),
      (hillEnergyChi q hq hr n x).re ≤ C) :
    hillRealGapIntegral q hq hr n 0 ≤ C*(hillRealLabels q hq hr (2*n)-hillRealLabels q hq hr (2*n-1))^2 := by
  by_cases hclosed : hillRealLabels q hq hr (2*n-1) = hillRealLabels q hq hr (2*n)
  · simp only [hillRealGapIntegral,hclosed,intervalIntegral.integral_same,mul_zero,sub_self,zero_pow (by norm_num : (2 : ℕ) ≠ 0),le_refl]
  have hab : hillRealLabels q hq hr (2*n-1) < hillRealLabels q hq hr (2*n) :=
    lt_of_le_of_ne (monotone_hillRealLabels q hq hr (by omega : 2*n-1 ≤ 2*n)) hclosed
  let a := hillRealLabels q hq hr (2*n-1)
  let b := hillRealLabels q hq hr (2*n)
  let c := hillGapCriticalPoint q hq hr n
  let H : ℝ → ℝ := fun x => (hillEnergyChi q hq hr n x).re
  have hc := (hillGapCriticalPoint_spec q hq hr n hn).1
  have hfilled (y : ℝ) (hy : y ∈ Icc a b) : (y : ℂ) ∈ hillGapFilledDomain q hq hr n :=
    hillGapSegment_subset_filledDomain q hq hr n hn
      (ofReal_mem_ordered_segment _ _ y (monotone_hillRealLabels q hq hr (by omega : 2*n-1 ≤ 2*n)) hy)
  have hH : ContinuousOn H (Icc a b) := continuous_re.comp_continuousOn
    ((analyticOnNhd_hillEnergyChi q hq hr n).continuousOn.comp continuous_ofReal.continuousOn hfilled)
  have hkernel := intervalIntegrable_gap_arcsine_kernel a b hab
  have hi : IntervalIntegrable (fun x => (c-x)^2*H x/Real.sqrt ((x-a)*(b-x))) volume a b := by
    simpa only [div_eq_mul_inv] using hkernel.continuousOn_mul
      (show ContinuousOn (fun x => (c-x)^2*H x) (uIcc a b) by
        rw [uIcc_of_le hab.le]
        exact ((continuousOn_const.sub continuousOn_id).pow 2).mul hH)
  have hj : IntervalIntegrable (fun x => (b-a)^2*C*(Real.sqrt ((x-a)*(b-x)))⁻¹) volume a b :=
    hkernel.const_mul _
  have hm := intervalIntegral.integral_mono_on hab.le hi hj (fun x hx => by
    have hax : |c-x| ≤ b-a := abs_le.mpr ⟨by dsimp only [c,a,b] at *; linarith [hc.1,hc.2,hx.1,hx.2],by dsimp only [c,a,b] at *; linarith [hc.1,hc.2,hx.1,hx.2]⟩
    have hsq : (c-x)^2 ≤ (b-a)^2 := by
      have hs := pow_le_pow_left₀ (abs_nonneg (c-x)) hax 2
      simpa only [sq_abs] using hs
    have hnum : (c-x)^2*H x ≤ (b-a)^2*C :=
      (mul_le_mul_of_nonneg_left (hbound x hx) (sq_nonneg (c-x))).trans
        (mul_le_mul_of_nonneg_right hsq hC)
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr (Real.sqrt_nonneg _)))
  rw [hillRealGapIntegral_eq_chi_integral q hq hr n hn]
  have hmul := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ 1/Real.pi)
  apply hmul.trans_eq
  rw [intervalIntegral.integral_const_mul,integral_gap_arcsine_kernel a b hab]
  field_simp [Real.pi_ne_zero]
  ring


end NLS.KdV
