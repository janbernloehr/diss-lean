import NLS.KdV.HillHminusHighDeflatedRoot
import NLS.KdV.HillHminusContourGapPhysicalGerms
import NLS.KdV.HillDeflatedRadicandFactorization
import NLS.ComplexAnalysis.DeflatedRootGerm

/-! # The actual free normalization of rough high deflated roots -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem hillHminus_high_root_free_square
    (n : ℕ+) (hn : 2 ≤ (n : ℕ)) (r : ℝ) (hr : 0 < r)
    (V : Set PeriodOneHminusOne) (hV : IsOpen V) (h0V : (0 : PeriodOneHminusOne) ∈ V)
    (hpairs : ∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u)
    (U : ℂ × PeriodOneHminusOne → ℂ)
    (hUa : AnalyticOnNhd ℂ U
      (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V))
    (hfac : ∀ t ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V,
      hillHminusRadicand t.2 t.1=hillHminusGapPolynomial n r t*(U t/(n : ℂ))^2) :
    (U ((((Real.pi : ℂ)*(n : ℕ))^2),0)/(n : ℂ))^2=
      hillDeflatedEnergyCanonicalRoot 0 h0q h0r (n : ℕ) (((Real.pi : ℂ)*(n : ℕ))^2)^2 := by
  let c : ℂ := ((Real.pi : ℂ)*(n : ℕ))^2
  have hc : (hillRealGapCenter 0 h0q h0r (n : ℕ) : ℂ)=c := by
    rw [hillFreeGapCenter h0q h0r (n : ℕ) n.property]
    simp only [freeHillValue,Int.cast_natCast,ofReal_mul,ofReal_pow,ofReal_natCast]
    dsimp only [c]
    ring
  have hR : 0 < Real.pi*(n : ℕ)*r := by positivity
  have hR0 : 0 < hillRealGapHalfLength 0 h0q h0r (n : ℕ)+hillRealGapCollar 0 h0q h0r (n : ℕ) :=
    add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r (n : ℕ) n.property).1
      (hillRealGapContour_geometry 0 h0q h0r (n : ℕ) n.property).2.1
  have hcf : c ∈ hillGapFilledDomain 0 h0q h0r (n : ℕ) := by
    apply hillRealGapContour_closedBall_subset_filledDomain 0 h0q h0r (n : ℕ) n.property
    rw [hc]
    exact mem_closedBall_self hR0.le
  have hU0 : AnalyticAt ℂ (fun z : ℂ => U (z,0)/(n : ℂ)) c :=
    ((hUa (c,0) ⟨mem_ball_self hR,h0V⟩).comp
      (f := fun z : ℂ => (z,(0 : PeriodOneHminusOne))) (analyticAt_id.prod analyticAt_const)).div_const
  have hB0 := analyticOnNhd_hillDeflatedEnergyCanonicalRoot 0 h0q h0r (n : ℕ) c hcf
  apply deflated_square_eq_at_center _ _ c hU0.continuousAt hB0.continuousAt
  filter_upwards [ball_mem_nhds c hR,(isOpen_hillGapFilledDomain 0 h0q h0r (n : ℕ)).mem_nhds hcf]
    with E hE hEf
  have hnew := hfac (E,0) ⟨hE,h0V⟩
  rw [hillHminusGapPolynomial_free h0q h0r n hn r hr V hV h0V hpairs E,
    hillHminusRadicand_zero_eq_hillL2] at hnew
  have hold := hillL2Radicand_eq_gap_polynomial_mul_deflated_sq 0 h0q h0r
    (n : ℕ) n.property E hEf
  simp only [map_zero] at hold
  have hv : (freeHillValue (n : ℕ) : ℂ)=c := by
    rw [← hillFreeGapCenter h0q h0r (n : ℕ) n.property]
    exact hc
  rw [(hillFreeGapEndpoints h0q h0r (n : ℕ) n.property).1,
    (hillFreeGapEndpoints h0q h0r (n : ℕ) n.property).2,hv] at hold
  simpa only [c,pow_two,mul_assoc] using hnew.symm.trans hold

include h0q h0r in
 theorem exists_hillHminus_free_normalized_high_roots :
    ∃ r C : ℝ, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < r ∧ r ≤ Real.pi/4 ∧ 0 < C ∧ 2 ≤ N ∧ IsOpen V ∧ (0 : PeriodOneHminusOne) ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → ∃ U : ℂ × PeriodOneHminusOne → ℂ,
        AnalyticOnNhd ℂ U
          (ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V) ∧
        (∀ a ∈ V, ∃ l u : ℂ, HillHminusHighGapPair a n r l u) ∧
        U ((((Real.pi : ℂ)*(n : ℕ))^2),0)=
          (n : ℂ)*hillDeflatedEnergyCanonicalRoot 0 h0q h0r (n : ℕ) (((Real.pi : ℂ)*(n : ℕ))^2) ∧
        ∀ t ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r) ×ˢ V,
          U t ≠ 0 ∧ ‖(U t)⁻¹‖ ≤ C ∧
          hillHminusRadicand t.2 t.1=hillHminusGapPolynomial n r t*(U t/(n : ℂ))^2 := by
  obtain ⟨r,C,N,V,hr,hrpi,hC,_hN,hV,h0V,hfamily⟩ := exists_hillHminus_high_deflated_roots 0
  refine ⟨r,C,max 2 N,V,hr,hrpi,hC,le_max_left _ _,hV,h0V,?_⟩
  intro n hn
  have hn2 : 2 ≤ (n : ℕ) := (le_max_left _ _).trans hn
  obtain ⟨U,hUa,hpairs,hprops⟩ := hfamily n ((le_max_right _ _).trans hn)
  let c : ℂ := ((Real.pi : ℂ)*(n : ℕ))^2
  have hR : 0 < Real.pi*(n : ℕ)*r := by positivity
  have hu0 := (hprops (c,0) ⟨mem_ball_self hR,h0V⟩).1
  have hsq := hillHminus_high_root_free_square h0q h0r n hn2 r hr V hV h0V hpairs U hUa
    (fun t ht => (hprops t ht).2.2)
  have hnn : (n : ℂ)≠0 := by exact_mod_cast n.ne_zero
  have hsqU : (U (c,0))^2=((n : ℂ)*hillDeflatedEnergyCanonicalRoot 0 h0q h0r (n : ℕ) c)^2 := by
    rw [div_pow] at hsq
    have hh := (div_eq_iff (pow_ne_zero 2 hnn)).mp hsq
    exact hh.trans (by ring)
  let a : ℂ := (n : ℂ)*hillDeflatedEnergyCanonicalRoot 0 h0q h0r (n : ℕ) c/U (c,0)
  have ha2 : a^2=1 := by
    dsimp only [a]
    rw [div_pow,← hsqU,div_self (pow_ne_zero 2 hu0)]
  have han : a≠0 := by
    intro ha
    simp only [ha,zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at ha2
    exact zero_ne_one ha2
  have ha1 : ‖a‖=1 := by
    have hh := congrArg norm ha2
    rw [norm_pow,norm_one] at hh
    nlinarith [norm_nonneg a]
  let W : ℂ × PeriodOneHminusOne → ℂ := fun t => a*U t
  refine ⟨W,analyticOnNhd_const.mul hUa,hpairs,?_,?_⟩
  · exact div_mul_cancel₀ _ hu0
  · intro t ht
    obtain ⟨hu,hb,hf⟩ := hprops t ht
    refine ⟨mul_ne_zero han hu,?_,?_⟩
    · change ‖(a*U t)⁻¹‖ ≤ C
      simpa only [mul_inv_rev,norm_mul,norm_inv,ha1,inv_one,mul_one] using hb
    · simpa only [W,div_pow,mul_pow,ha2,one_mul] using hf

end NLS.KdV
