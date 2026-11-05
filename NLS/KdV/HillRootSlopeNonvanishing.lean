import NLS.KdV.HillAbelianRootSlope
import NLS.KdV.HillGapRootHilbertCoordinates
import NLS.KdV.HillGlobalGapPeriodCriterion

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



theorem hillGapRootHilbertCoordinates_star
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr) :
    star (hillGapRootHilbertCoordinates q hq hr roots hroots) =
      hillGapRootHilbertCoordinates q hq hr roots hroots := by
  ext j
  rw [lp.star_apply]
  change star (hillGapRootScaledOffset roots j) = hillGapRootScaledOffset roots j
  unfold hillGapRootScaledOffset
  split_ifs
  · simp only [Complex.star_def,map_div₀,conj_ofReal,map_intCast]
  · exact star_zero _

theorem hillAbelianRootSlope_ne_zero_on_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (E : ℂ)
    (hE : E ∈ segment ℝ (hillRealLabels q hq hr (2*m-1) : ℂ) (hillRealLabels q hq hr (2*m) : ℂ)) :
    hillAbelianRootSlope n m E (hillGapRootHilbertCoordinates q hq hr roots hroots) ≠ 0 := by
  let a := hillGapRootHilbertCoordinates q hq hr roots hroots
  intro hzero
  obtain ⟨j,_,he⟩ := (hillAbelianHilbertPsi_zero_iff n hn E (hillAbelianRootUpdate m (a,E+1))).mp hzero
  change hillAbelianHilbertRootEnergy (hillAbelianRootUpdate m (a,E+1)) (j+1) = E at he
  by_cases hjm : j+1 = m
  · rw [hjm,hillAbelianHilbertRootEnergy_update_same m hm a (E+1)] at he
    have hh : (1:ℂ) = 0 := by linear_combination he
    exact one_ne_zero hh
  · rw [hillAbelianHilbertRootEnergy_update_other m (j+1) hjm a (E+1)] at he
    have hrec := hillGapRootHilbertCoordinates_reconstruct q hq hr roots hroots j
    change (roots j:ℂ) = hillAbelianHilbertRootEnergy a (j+1) at hrec
    have hx := re_mem_Icc_of_mem_real_segment _ _
      (monotone_hillRealLabels q hq hr (by omega : 2*m-1 ≤ 2*m)) E hE
    have heR : roots j = E.re := by simpa only [ofReal_re] using congrArg Complex.re (hrec.trans he)
    have hroot := hroots j
    rcases hillRealGap_exterior_to_other_gap q hq hr m (j+1) hm (by omega) hjm E.re hx with hl | hu
    · linarith [hroot.1]
    · linarith [hroot.2]

theorem hillAbelianRootSlope_period_ne_zero
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (2*(Real.pi:ℂ))⁻¹ * ∮ E in C((hillRealGapCenter q hq hr m : ℂ),
      hillRealGapHalfLength q hq hr m+hillRealGapCollar q hq hr m),
      hillAbelianRootSlope n m E (hillGapRootHilbertCoordinates q hq hr roots hroots)/
        hillEnergyCanonicalRootProduct q hq hr E ≠ 0 := by
  intro hzero
  obtain ⟨E,hE,hEz⟩ := exists_zero_on_hillRealGap_of_intrinsic_period_zero q hq hr
    (fun E => hillAbelianRootSlope n m E (hillGapRootHilbertCoordinates q hq hr roots hroots))
    (analyticOnNhd_hillAbelianRootSlope n m _) m hm
    (fun x _ => hillAbelianRootSlope_im_eq_zero n m _ (hillGapRootHilbertCoordinates_star q hq hr roots hroots) x)
    hzero
  exact hillAbelianRootSlope_ne_zero_on_gap q hq hr roots hroots n m hn hm E hE hEz

end NLS.KdV
