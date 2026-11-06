import NLS.KdV.HillFilledFreeGapUnit

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFilledFreeGapUnit_bounded_complex_analytic (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ k : ℕ, N ≤ k →
      AnalyticOnNhd ℂ (hillFilledFreeGapUnit h0q h0r k) (univ ×ˢ ball (0 : Coeff 2) B) := by
  obtain ⟨Np,hNp,hpairs⟩ := exists_hillFreeGap_bounded_complex_localized_pairs h0q h0r (1/16) (by norm_num) (by norm_num) B
  obtain ⟨Nu,hNu,hunit⟩ := exists_hillFreeGap_bounded_complex_analytic_unit h0q h0r B
  obtain ⟨Ns,hNs,hdata⟩ := exists_hillFreeGap_bounded_complex_analytic_symmetric_data h0q h0r B
  refine ⟨max Np (max Nu Ns),hNp.trans (le_max_left _ _),?_⟩
  intro k hk
  have hkp : Np ≤ k := (le_max_left _ _).trans hk
  have hku : Nu ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hks : Ns ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  have hk1 : 1 ≤ k := hNp.trans hkp
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  let V := ball (0 : Coeff 2) B
  let W := (closedBall c (R/2))ᶜ ×ˢ V
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hW : IsOpen W := isClosed_closedBall.isOpen_compl.prod isOpen_ball
  obtain ⟨hM,hS,_⟩ := hdata k hks
  have hP : AnalyticOnNhd ℂ (fun t : ℂ × Coeff 2 => hillLocalGapPolynomial 0 h0q h0r k t.2 t.1) (univ ×ˢ V) := by
    intro t ht
    exact ((analyticAt_fst.sub ((hM t.2 ht.2).comp analyticAt_snd)).pow 2).sub
      (((hS t.2 ht.2).comp analyticAt_snd).div_const)
  have hPn (t : ℂ × Coeff 2) (ht : t ∈ W) : hillLocalGapPolynomial 0 h0q h0r k t.2 t.1≠0 := by
    have hp : ‖t.2‖ ≤ B := (show ‖t.2‖ < B by simpa only [V,mem_ball,dist_zero_right] using ht.2).le
    obtain ⟨hb,a,ha,b,hb',haz,hbz,hm⟩ := hpairs t.2 hp k hkp
    have haK : a ∈ closedBall c (R/2) := closedBall_subset_closedBall (by linarith : (1/16)*R ≤ R/2) (ball_subset_closedBall ha)
    have hbK : b ∈ closedBall c (R/2) := closedBall_subset_closedBall (by linarith : (1/16)*R ≤ R/2) (ball_subset_closedBall hb')
    have haB : a ∈ ball c R := ball_subset_ball (by linarith : (1/16)*R ≤ R) ha
    have hbB : b ∈ ball c R := ball_subset_ball (by linarith : (1/16)*R ≤ R) hb'
    rw [hillLocalGapPolynomial_eq_of_pair 0 h0q h0r k hk1 t.2 hb haB hbB hm]
    exact mul_ne_zero (sub_ne_zero.mpr (fun he => ht.1 (he ▸ haK)))
      (sub_ne_zero.mpr (fun he => ht.1 (he ▸ hbK)))
  have hquot : AnalyticOnNhd ℂ (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1/hillLocalGapPolynomial 0 h0q h0r k t.2 t.1) W := by
    intro t ht
    exact (analyticOnNhd_hillL2Radicand_joint t (mem_univ _)).div (hP t ⟨mem_univ _,ht.2⟩) (hPn t ht)
  have heq (t : ℂ × Coeff 2) (ht : t ∈ W) :
      hillFilledFreeGapUnit h0q h0r k t=hillL2Radicand t.2 t.1/hillLocalGapPolynomial 0 h0q h0r k t.2 t.1 := by
    by_cases hE : t.1 ∈ ball c R
    · rw [hillFilledFreeGapUnit,if_pos hE]
      have hf := ((hunit k hku).2 t.2 ht.2 t.1 hE).1
      rw [hf]
      exact (mul_div_cancel_left₀ _ (hPn t ht)).symm
    · exact if_neg hE
  intro t ht
  by_cases hE : t.1 ∈ ball c R
  · apply ((hunit k hku).1 t ⟨hE,ht.2⟩).congr
    filter_upwards [(isOpen_ball.prod isOpen_ball).mem_nhds (show t ∈ ball c R ×ˢ V from ⟨hE,ht.2⟩)] with u hu
    exact (hillFilledFreeGapUnit_eq_local h0q h0r k u.2 u.1 hu.1).symm
  · have htW : t ∈ W := by
      refine ⟨?_,ht.2⟩
      intro hhalf
      have hd : dist t.1 c ≤ R/2 := hhalf
      apply hE
      exact lt_of_le_of_lt hd (by linarith)
    apply (hquot t htW).congr
    filter_upwards [hW.mem_nhds htW] with u hu
    exact (heq u hu).symm

end NLS.KdV
