import NLS.KdV.HillL2RealContourMoments
import NLS.KdV.HillEnergyRadicandProduct
import NLS.KdV.HillL2BandPhase
import NLS.ComplexAnalysis.RealCutConnected
import NLS.ComplexAnalysis.RealEndpointRootSigns

/-! # The actual normalized Hill root equals the energy canonical root product on the entire real cut domain. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillEnergyRootProduct_real_first_band
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (x : ℝ)
    (hx : x ∈ Ioo (hillRealLabels q hq hr 0) (hillRealLabels q hq hr 1)) :
    0 < (hillEnergyRootProduct q hq hr x).re ∧ (hillEnergyRootProduct q hq hr x).im = 0 := by
  have hf (k : ℕ) : 0 < (hillEnergyRootFactor q hq hr (k+1) x).re ∧
      (hillEnergyRootFactor q hq hr (k+1) x).im = 0 := by
    have he := endpointRoot_real_left (hillRealLabels q hq hr (2*(k+1)-1))
      (hillRealLabels q hq hr (2*(k+1))) x
      (monotone_hillRealLabels q hq hr (by omega))
      (hx.2.trans_le (monotone_hillRealLabels q hq hr (by omega)))
    have hfree : 0 < freeHillValue (k+1) := by
      unfold freeHillValue
      apply mul_pos (sq_pos_of_ne_zero Real.pi_ne_zero) (sq_pos_of_ne_zero _)
      exact_mod_cast (show (k+1 : ℤ) ≠ 0 by omega)
    simp only [hillEnergyRootFactor,div_ofReal_re,div_ofReal_im]
    exact ⟨div_pos he.1 hfree, by rw [he.2,zero_div]⟩
  have he (k : ℕ) : hillEnergyRootFactor q hq hr (k+1) x =
      ((hillEnergyRootFactor q hq hr (k+1) x).re : ℂ) := by
    apply Complex.ext
    · simp only [ofReal_re]
    · simpa only [ofReal_im] using (hf k).2
  have hp := (multipliable_hillEnergyRootFactors q hq hr (x : ℂ)).hasProd.tendsto_prod_nat
  have hpartial (N : ℕ) : (∏ k ∈ Finset.range N, hillEnergyRootFactor q hq hr (k+1) x) =
      ((∏ k ∈ Finset.range N, (hillEnergyRootFactor q hq hr (k+1) x).re : ℝ) : ℂ) := by
    push_cast
    exact Finset.prod_congr rfl (fun k _ => he k)
  have him : (hillEnergyRootProduct q hq hr x).im = 0 := by
    have h := continuous_im.continuousAt.tendsto.comp hp
    change Tendsto (fun N => (∏ k ∈ Finset.range N, hillEnergyRootFactor q hq hr (k+1) x).im) atTop _ at h
    simp only [hpartial,ofReal_im] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hre : 0 ≤ (hillEnergyRootProduct q hq hr x).re := by
    apply ge_of_tendsto (continuous_re.continuousAt.tendsto.comp hp)
    filter_upwards with N
    change 0 ≤ (∏ k ∈ Finset.range N, hillEnergyRootFactor q hq hr (k+1) x).re
    rw [hpartial,ofReal_re]
    exact (Finset.prod_pos (fun k _ => (hf k).1)).le
  have hz : (x : ℂ) ∈ hillL2RealCutDomain q hq hr := Or.inr ⟨0,by simpa using hx⟩
  have hne := hillEnergyRootProduct_ne_zero q hq hr x
    (not_mem_hillGapSegment_of_mem_realCutDomain q hq hr x hz)
  refine ⟨lt_of_le_of_ne hre ?_,him⟩
  intro heq
  apply hne
  apply Complex.ext <;> simp [heq,him]


theorem hillEnergyCanonicalRootProduct_im_neg_first_band
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (x : ℝ)
    (hx : x ∈ Ioo (hillRealLabels q hq hr 0) (hillRealLabels q hq hr 1)) :
    (hillEnergyCanonicalRootProduct q hq hr x).im < 0 := by
  obtain ⟨hp,hi⟩ := hillEnergyRootProduct_real_first_band q hq hr x hx
  have hs : Complex.sqrt ((x : ℂ)-hillRealLabels q hq hr 0) =
      (Real.sqrt (x-hillRealLabels q hq hr 0) : ℂ) := by
    rw [← ofReal_sub,Complex.sqrt_of_nonneg (by exact_mod_cast (show 0 ≤ x-hillRealLabels q hq hr 0 by linarith [hx.1]))]
    simp only [ofReal_re]
  have hpos : 0 < Real.sqrt (x-hillRealLabels q hq hr 0) := Real.sqrt_pos.mpr (by linarith [hx.1])
  simp only [hillEnergyCanonicalRootProduct,hs,mul_im,mul_re,neg_re,neg_im,
    I_re,I_im,ofReal_re,ofReal_im,hi]
  norm_num at ⊢
  nlinarith

theorem hillL2RealCutRoot_im_neg_first_band
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (x : ℝ)
    (hx : x ∈ Ioo (hillRealLabels q hq hr 0) (hillRealLabels q hq hr 1)) :
    (hillL2RealCutRoot (SpectralWeight.one.toCoeff q) x).im < 0 := by
  have hre := hillL2UpperBoundaryPrimitive_re_eq_zero_band q hq hr 0 x (by simpa using hx)
  have hphase := hillL2UpperBoundaryPrimitive_band_phase q hq hr 0 x (by simpa using hx)
  simp only [Nat.cast_zero,zero_mul,zero_add,one_mul,mem_Ioo] at hphase
  have hs : Real.sin (hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x).im < 0 := Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [hphase.1]) (by linarith [hphase.2])
  simp only [hillL2RealCutRoot,hillL2RealCutPrimitive,ofReal_im,if_true,ofReal_re,
    mul_im]
  norm_num
  have hrepr : hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x =
      ((hillL2UpperBoundaryPrimitive (SpectralWeight.one.toCoeff q) x).im : ℂ)*I := by
    apply Complex.ext <;> simp [hre]
  rw [hrepr,Complex.sinh_mul_I]
  rw [← Complex.ofReal_sin]
  simp only [mul_im,ofReal_re,I_im,ofReal_im,I_re,mul_one,mul_zero,add_zero]
  linarith


theorem isPreconnected_hillL2RealCutDomain
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    IsPreconnected (hillL2RealCutDomain q hq hr) :=
  isPreconnected_of_contains_nonreal_and_real_interval _
    (hillRealLabels q hq hr 0) (hillRealLabels q hq hr 1)
    (by simpa using hillRealLabels_band_strict q hq hr 0)
    (fun _ hi => Or.inl hi) (fun _ hx => Or.inr ⟨0,by simpa using hx⟩)

theorem hillEnergyCanonicalRootProduct_eq_realCutRoot
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    EqOn (hillEnergyCanonicalRootProduct q hq hr)
      (hillL2RealCutRoot (SpectralWeight.one.toCoeff q)) (hillL2RealCutDomain q hq hr) := by
  let x : ℝ := (hillRealLabels q hq hr 0+hillRealLabels q hq hr 1)/2
  have hband := hillRealLabels_band_strict q hq hr 0
  have hx : x ∈ Ioo (hillRealLabels q hq hr 0) (hillRealLabels q hq hr 1) := by
    dsimp only [x]
    simp only [mul_zero,zero_add] at hband
    constructor <;> linarith
  have hxcut : (x : ℂ) ∈ hillL2RealCutDomain q hq hr := Or.inr ⟨0,by simpa using hx⟩
  have hsq (z : ℂ) (hz : z ∈ hillL2RealCutDomain q hq hr) :
      hillEnergyCanonicalRootProduct q hq hr z^2 = hillL2RealCutRoot (SpectralWeight.one.toCoeff q) z^2 :=
    (hillEnergyCanonicalRootProduct_sq_eq_radicand q hq hr z hz).trans
      (hillL2RealCutRoot_sq q hq hr z).symm
  have he : hillEnergyCanonicalRootProduct q hq hr x = hillL2RealCutRoot (SpectralWeight.one.toCoeff q) x := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hsq x hxcut) with he | he
    · exact he
    · have hp := hillEnergyCanonicalRootProduct_im_neg_first_band q hq hr x hx
      have hr' := hillL2RealCutRoot_im_neg_first_band q hq hr x hx
      have hi := congrArg Complex.im he
      simp only [neg_im] at hi
      linarith
  exact (isPreconnected_hillL2RealCutDomain q hq hr).eq_of_sq_eq
    (analyticOnNhd_hillEnergyCanonicalRootProduct q hq hr).continuousOn
    ((Complex.continuous_sinh.comp_continuousOn (analyticOnNhd_hillL2RealCutPrimitive q hq hr).continuousOn).const_mul 2)
    hsq (fun hz => hillL2RealCutRoot_ne_zero q hq hr _ hz) hxcut he



/-- The actual logarithmic differential uses precisely the energy product root. -/
theorem hasDerivAt_hillL2RealCutPrimitive_energyProduct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (z : ℂ)
    (hz : z ∈ hillL2RealCutDomain q hq hr) :
    HasDerivAt (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q))
      (deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
        hillEnergyCanonicalRootProduct q hq hr z) z := by
  rw [hillEnergyCanonicalRootProduct_eq_realCutRoot q hq hr hz]
  exact hasDerivAt_hillL2RealCutPrimitive q hq hr z hz

/-- The exact source canonical-root Arnold formula, at every gap and level. -/
theorem hillL2RealContourMoment_arnold_energyProduct
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    hillL2RealContourMoment q hq hr n m = ((m + 1 : ℂ) * (Real.pi : ℂ))⁻¹ *
      ∮ z in C((hillRealGapCenter q hq hr n : ℂ),
          hillRealGapHalfLength q hq hr n + hillRealGapCollar q hq hr n),
        z ^ (m + 1) * deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
          hillEnergyCanonicalRootProduct q hq hr z := by
  rw [hillL2RealContourMoment_arnold_level q hq hr n hn m]
  congr 1
  obtain ⟨hd,hη,_⟩ := hillRealGapContour_geometry q hq hr n hn
  apply circleIntegral.integral_congr (add_nonneg hd hη.le)
  intro z hz
  dsimp only
  rw [hillEnergyCanonicalRootProduct_eq_realCutRoot q hq hr
    (hillRealGapContour_sphere_subset q hq hr n hn hz)]

end NLS.KdV
