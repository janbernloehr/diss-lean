import NLS.KdV.HillHminusOriginalGapPairs
import NLS.KdV.HillPhysicalRealGermIdentity
import NLS.KdV.HillHminusLocalGapMoments

/-! # The intrinsic high polynomial has the original complex L2 germ -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillHminusGapPolynomial_physical_germ
    (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (r : ℝ) (hr : 0 < r)
    (V : Set PeriodOneHminusOne) (hV : IsOpen V) (h0V : (0 : PeriodOneHminusOne) ∈ V)
    (hpairs : ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩, ∀ E : ℂ,
      hillHminusGapPolynomial n r (E,hillOriginalHminusSource p.val)=
        hillLocalGapPolynomial 0 h0q h0r (n : ℕ) (SpectralWeight.one.toCoeff p.val) E := by
  let b : ℝ := min ((n : ℝ)/8) (Real.pi*(n : ℕ)*r/4)
  have hb : 0 < b := by dsimp only [b]; positivity
  let W : Set RealPeriodOneHillPotential :=
    {p | hillOriginalHminusSource p.val ∈ V ∧ ‖p.val‖ < b}
  have hW : IsOpen W :=
    (hV.preimage (hillOriginalHminusSource.continuous.comp continuous_subtype_val)).inter
      (isOpen_lt continuous_subtype_val.norm continuous_const)
  have h0W : (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential) ∈ W := by
    change hillOriginalHminusSource 0 ∈ V ∧ ‖(0 : WeightedCoeff SpectralWeight.one.toWeight 2)‖ < b
    simpa only [map_zero,norm_zero] using And.intro h0V hb
  obtain ⟨W0,hW0,h0W0,hdata⟩ :=
    exists_hillLocalGapSymmetricData_physical_neighborhood 0 h0q h0r (n : ℕ) n.property
  filter_upwards [hW.mem_nhds h0W,hW0.mem_nhds h0W0] with p hp hp0
  have hcut : 8*‖p.val‖ ≤ (n : ℝ) := by
    have hh := hp.2.trans_le (min_le_left ((n : ℝ)/8) (Real.pi*(n : ℕ)*r/4))
    linarith
  have hbound : 4*‖p.val‖ ≤ Real.pi*(n : ℕ)*r := by
    have hh := hp.2.trans_le (min_le_right ((n : ℝ)/8) (Real.pi*(n : ℕ)*r/4))
    linarith
  obtain ⟨l,u,hpair⟩ := hpairs _ hp.1
  intro E
  rw [hillHminusGapPolynomial_original_labels p n hn r hr l u hpair hcut hbound E]
  rw [hillLocalGapPolynomial,(hdata p hp0).1,(hdata p hp0).2]
  simp only [hillRealGapCenter,hillRealGapHalfLength,ofReal_div,ofReal_add,ofReal_sub,ofReal_ofNat]
  ring

theorem hillHminusGapPolynomial_original_label_germ
    (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (r : ℝ) (hr : 0 < r)
    (V : Set PeriodOneHminusOne) (hV : IsOpen V) (h0V : (0 : PeriodOneHminusOne) ∈ V)
    (hpairs : ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u) :
    ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 ⟨0,h0q,h0r⟩, ∀ E : ℂ,
      hillHminusGapPolynomial n r (E,hillOriginalHminusSource p.val)=
        (E-(hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ)-1) : ℂ))*
          (E-(hillRealLabels p.val p.property.1 p.property.2 (2*(n : ℕ)) : ℂ)) := by
  obtain ⟨W,hW,h0W,hdata⟩ :=
    exists_hillLocalGapSymmetricData_physical_neighborhood 0 h0q h0r (n : ℕ) n.property
  filter_upwards [hillHminusGapPolynomial_physical_germ h0q h0r n hn r hr V hV h0V hpairs,
    hW.mem_nhds h0W] with p hp hpW
  intro E
  rw [hp E,hillLocalGapPolynomial,(hdata p hpW).1,(hdata p hpW).2]
  simp only [hillRealGapCenter,hillRealGapHalfLength,ofReal_div,ofReal_add,ofReal_sub,ofReal_ofNat]
  ring

theorem hillHminusGapPolynomial_l2_germ
    (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (r : ℝ) (hr : 0 < r)
    (V : Set PeriodOneHminusOne) (hV : IsOpen V) (h0V : (0 : PeriodOneHminusOne) ∈ V)
    (hpairs : ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u) :
    ∀ᶠ u : Coeff 2 in 𝓝 0, ∀ E : ℂ,
      hillHminusGapPolynomial n r (E,periodOneL2Inclusion u)=
        hillLocalGapPolynomial 0 h0q h0r (n : ℕ) (Coeff.periodDouble u) E := by
  have hP := analyticOnNhd_hillHminusGapPolynomial n r hr V hV hpairs
  obtain ⟨W,_hW,h0W,hM,hS,_⟩ :=
    exists_hillLocalGapSymmetricData_analytic_neighborhood 0 h0q h0r (n : ℕ) n.property
  have hM0 : AnalyticAt ℂ (hillLocalGapMidpoint 0 h0q h0r (n : ℕ)) 0 := by
    simpa only [map_zero] using hM _ h0W
  have hS0 : AnalyticAt ℂ (hillLocalGapSquare 0 h0q h0r (n : ℕ)) 0 := by
    simpa only [map_zero] using hS _ h0W
  have hm : AnalyticAt ℂ (fun u : Coeff 2 =>
      hillLocalGapMidpoint 0 h0q h0r (n : ℕ) (Coeff.periodDouble u)) 0 := by
    have ha : AnalyticAt ℂ (hillLocalGapMidpoint 0 h0q h0r (n : ℕ)) (Coeff.periodDouble (0 : Coeff 2)) :=
      by simpa only [map_zero] using hM0
    exact ha.comp (f := fun u : Coeff 2 => Coeff.periodDouble u) (Coeff.periodDouble.toContinuousLinearMap.analyticAt 0)
  have hs : AnalyticAt ℂ (fun u : Coeff 2 =>
      hillLocalGapSquare 0 h0q h0r (n : ℕ) (Coeff.periodDouble u)) 0 := by
    have ha : AnalyticAt ℂ (hillLocalGapSquare 0 h0q h0r (n : ℕ)) (Coeff.periodDouble (0 : Coeff 2)) :=
      by simpa only [map_zero] using hS0
    exact ha.comp (f := fun u : Coeff 2 => Coeff.periodDouble u) (Coeff.periodDouble.toContinuousLinearMap.analyticAt 0)
  have hpoint (E : ℂ) : (fun u => hillHminusGapPolynomial n r (E,periodOneL2Inclusion u))
      =ᶠ[𝓝 (0 : Coeff 2)] (fun u => hillLocalGapPolynomial 0 h0q h0r (n : ℕ) (Coeff.periodDouble u) E) := by
    have hPa : AnalyticAt ℂ (fun u => hillHminusGapPolynomial n r (E,periodOneL2Inclusion u)) 0 := by
      have ha : AnalyticAt ℂ (hillHminusGapPolynomial n r) (E,periodOneL2Inclusion (0 : Coeff 2)) :=
        by simpa only [map_zero] using hP (E,0) ⟨mem_univ _,h0V⟩
      exact ha.comp (f := fun u : Coeff 2 => (E,periodOneL2Inclusion u))
        (analyticAt_const.prod (periodOneL2Inclusion.analyticAt 0))
    have hQa : AnalyticAt ℂ (fun u => hillLocalGapPolynomial 0 h0q h0r (n : ℕ) (Coeff.periodDouble u) E) 0 :=
      ((analyticAt_const.sub hm).pow 2).sub (hs.div_const)
    apply eventuallyEq_native_of_physical_real_germ h0q h0r _ _ hPa hQa
    filter_upwards [hillHminusGapPolynomial_physical_germ h0q h0r n hn r hr V hV h0V hpairs] with p hp
    change hillHminusGapPolynomial n r (E,hillOriginalHminusSource p.val)=
      hillLocalGapPolynomial 0 h0q h0r (n : ℕ)
        (Coeff.periodDouble (Fourier.paritySample 0 (SpectralWeight.one.toCoeff p.val))) E
    rw [hillPeriodDouble_unitSample _ p.property.1]
    exact hp E
  filter_upwards [hpoint 0,hpoint 1] with u hu0 hu1
  intro E
  have hleft : hillHminusGapPolynomial n r (E,periodOneL2Inclusion u)=E^2+
      (hillHminusGapPolynomial n r (1,periodOneL2Inclusion u)-
        hillHminusGapPolynomial n r (0,periodOneL2Inclusion u)-1)*E+
          hillHminusGapPolynomial n r (0,periodOneL2Inclusion u) := by
    unfold hillHminusGapPolynomial momentPairPolynomial
    ring
  have hright : hillLocalGapPolynomial 0 h0q h0r (n : ℕ) (Coeff.periodDouble u) E=E^2+
      (hillLocalGapPolynomial 0 h0q h0r (n : ℕ) (Coeff.periodDouble u) 1-
        hillLocalGapPolynomial 0 h0q h0r (n : ℕ) (Coeff.periodDouble u) 0-1)*E+
          hillLocalGapPolynomial 0 h0q h0r (n : ℕ) (Coeff.periodDouble u) 0 := by
    unfold hillLocalGapPolynomial
    ring
  rw [hleft,hright,hu0,hu1]

include h0q h0r in
theorem hillHminusGapPolynomial_free
    (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (r : ℝ) (hr : 0 < r)
    (V : Set PeriodOneHminusOne) (hV : IsOpen V) (h0V : (0 : PeriodOneHminusOne) ∈ V)
    (hpairs : ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u) (E : ℂ) :
    hillHminusGapPolynomial n r (E,0)=(E-((Real.pi : ℂ)*(n : ℕ))^2)^2 := by
  have h := (hillHminusGapPolynomial_l2_germ h0q h0r n hn r hr V hV h0V hpairs).self_of_nhds E
  simp only [map_zero] at h
  have hdata := hillLocalGapSymmetricData_eq_physical_of_geometry 0 h0q h0r 0 h0q h0r
    (n : ℕ) n.property (hillRealGapContour_band_bounds 0 h0q h0r (n : ℕ) n.property)
    (hillRealGapSegment_subset_intrinsic_contour_ball 0 h0q h0r (n : ℕ) n.property)
  simp only [map_zero] at hdata
  rw [h,hillLocalGapPolynomial,hdata.1,hdata.2,hillFreeGapHalfLength h0q h0r (n : ℕ) n.property]
  rw [hillRealGapCenter,(hillFreeGapEndpoints h0q h0r (n : ℕ) n.property).1,
    (hillFreeGapEndpoints h0q h0r (n : ℕ) n.property).2]
  simp only [freeHillValue,Int.cast_natCast,ofReal_div,ofReal_add,ofReal_mul,ofReal_pow,ofReal_natCast,
    ofReal_ofNat,ofReal_zero]
  ring

end NLS.KdV
