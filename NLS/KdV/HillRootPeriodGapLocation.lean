import NLS.KdV.HillRootPeriodAffineFormula
import NLS.KdV.HillHilbertNumeratorReality

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillAbelianPeriodRoot_mem_gap
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ≠ n) :
    hillAbelianPeriodRoot q hq hr roots hroots n m ∈
      segment ℝ (hillRealLabels q hq hr (2*m-1) : ℂ) (hillRealLabels q hq hr (2*m) : ℂ) := by
  let a := hillGapRootHilbertCoordinates q hq hr roots hroots
  let s := hillAbelianPeriodRoot q hq hr roots hroots n m
  have ha : star a = a := hillGapRootHilbertCoordinates_star q hq hr roots hroots
  have hs : conj s = s := Complex.conj_eq_iff_im.mpr (hillAbelianPeriodRoot_im_eq_zero q hq hr roots hroots n m hm)
  have hu : star (hillAbelianRootUpdate m (a,s)) = hillAbelianRootUpdate m (a,s) := by
    have h := hillAbelianRootUpdate_star m a s
    simpa only [ha,hs] using h.symm
  obtain ⟨E,hE,hzero⟩ := exists_zero_on_hillRealGap_of_intrinsic_period_zero q hq hr
    (fun E => hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (a,s)))
    (analyticOnNhd_hillAbelianHilbertPsi_rootUpdate_energy n m a s) m hm
    (fun x _ => hillAbelianHilbertPsi_im_eq_zero_of_real_roots n _ hu x)
    (hillAbelianPeriodRoot_period_eq_zero q hq hr roots hroots n m hn hm hmn)
  obtain ⟨j,_,he⟩ := (hillAbelianHilbertPsi_zero_iff n hn E (hillAbelianRootUpdate m (a,s))).mp hzero
  change hillAbelianHilbertRootEnergy (hillAbelianRootUpdate m (a,s)) (j+1) = E at he
  by_cases hjm : j+1 = m
  · rw [hjm,hillAbelianHilbertRootEnergy_update_same m hm a s] at he
    change s ∈ segment ℝ (hillRealLabels q hq hr (2*m-1) : ℂ) (hillRealLabels q hq hr (2*m) : ℂ)
    rw [he]
    exact hE
  · rw [hillAbelianHilbertRootEnergy_update_other m (j+1) hjm a s] at he
    have hrec := hillGapRootHilbertCoordinates_reconstruct q hq hr roots hroots j
    change (roots j:ℂ) = hillAbelianHilbertRootEnergy a (j+1) at hrec
    have hx := re_mem_Icc_of_mem_real_segment _ _
      (monotone_hillRealLabels q hq hr (by omega : 2*m-1 ≤ 2*m)) E hE
    have heR : roots j = E.re := by simpa only [ofReal_re] using congrArg Complex.re (hrec.trans he)
    have hroot := hroots j
    rcases hillRealGap_exterior_to_other_gap q hq hr m (j+1) hm (by omega) hjm E.re hx with hl | hu
    · exfalso; linarith [hroot.1]
    · exfalso; linarith [hroot.2]

theorem hillAbelianPeriodRoot_re_mem_gap
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ≠ n) :
    (hillAbelianPeriodRoot q hq hr roots hroots n m).re ∈
      Icc (hillRealLabels q hq hr (2*m-1)) (hillRealLabels q hq hr (2*m)) :=
  re_mem_Icc_of_mem_real_segment _ _ (monotone_hillRealLabels q hq hr (by omega : 2*m-1 ≤ 2*m)) _
    (hillAbelianPeriodRoot_mem_gap q hq hr roots hroots n m hn hm hmn)

theorem hillAbelianPeriodRoot_unique
    (roots : ℕ → ℝ) (hroots : roots ∈ hillGapRootBox q hq hr)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hmn : m ≠ n) (s : ℂ)
    (hperiod : hillIntrinsicGapPeriod q hq hr m (fun E => hillAbelianHilbertPsi n
      (E,hillAbelianRootUpdate m (hillGapRootHilbertCoordinates q hq hr roots hroots,s))) = 0) :
    s = hillAbelianPeriodRoot q hq hr roots hroots n m := by
  have hA := hillAbelianRootSlope_period_ne_zero q hq hr roots hroots n m hn hm
  change hillIntrinsicGapPeriod q hq hr m (fun E => hillAbelianRootSlope n m E
    (hillGapRootHilbertCoordinates q hq hr roots hroots)) ≠ 0 at hA
  rw [hillIntrinsicGapPeriod_rootUpdate_affine q hq hr n m hm hmn] at hperiod
  unfold hillAbelianPeriodRoot
  apply (eq_div_iff hA).mpr
  linear_combination hperiod

end NLS.KdV
