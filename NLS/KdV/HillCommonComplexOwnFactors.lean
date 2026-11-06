import NLS.KdV.HillComplexDirichletTerminal
import NLS.KdV.HillUniformComplexGapData

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillComplexOwnGapFactor (k : ℕ) (p : Coeff 2) : ℂ :=
  hillLocalGapMidpoint 0 h0q h0r k p-hillScaledDirichletRoot h0q h0r (1/16) k p+
    hillComplexDirichletGapTerminal h0q h0r k p

def hillComplexOwnGapDualFactor (k : ℕ) (p : Coeff 2) : ℂ :=
  hillLocalGapMidpoint 0 h0q h0r k p-hillScaledDirichletRoot h0q h0r (1/16) k p-
    hillComplexDirichletGapTerminal h0q h0r k p

theorem exists_hillComplexOwnGapFactors_common_analytic_bound (B : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ k : ℕ, N≤k →
      AnalyticOnNhd ℂ (hillComplexOwnGapFactor h0q h0r k) (ball (0 : Coeff 2) B) ∧
      AnalyticOnNhd ℂ (hillComplexOwnGapDualFactor h0q h0r k) (ball (0 : Coeff 2) B) ∧
      ∀ p ∈ ball (0 : Coeff 2) B,
        hillComplexOwnGapFactor h0q h0r k p*hillComplexOwnGapDualFactor h0q h0r k p=
          hillLocalGapSquare 0 h0q h0r k p/4 ∧
        ‖hillComplexOwnGapFactor h0q h0r k p‖ ≤
          (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/4 ∧
        ‖hillComplexOwnGapDualFactor h0q h0r k p‖ ≤
          (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/4 := by
  obtain ⟨Nt,hNt,ht⟩ := exists_hillComplexDirichletGapTerminal_analytic_bound h0q h0r B
  obtain ⟨Nm,hNm,hm⟩ := exists_hillFreeGap_bounded_complex_analytic_symmetric_data h0q h0r B
  obtain ⟨Nd,hNd,hd⟩ := exists_hillScaledDirichletRoot_bounded_complex_analytic_chart h0q h0r (1/16) (by norm_num) (by norm_num) B
  obtain ⟨Np,hNp,hpairs⟩ := exists_hillFreeGap_bounded_complex_localized_pairs h0q h0r (1/16) (by norm_num) (by norm_num) B
  refine ⟨Nt+Nm+Nd+Np,hNt.trans (by omega),?_⟩
  intro k hk
  have hkt : Nt≤k := by omega
  have hkm : Nm≤k := by omega
  have hkd : Nd≤k := by omega
  have hkp : Np≤k := by omega
  have hk1 := hNt.trans hkt
  have hbase := ((hm k hkm).1.sub (hd k hkd).1)
  refine ⟨hbase.add (ht k hkt).1,hbase.sub (ht k hkt).1,?_⟩
  intro p hp
  have hpB : ‖p‖≤B := (show ‖p‖<B by simpa only [mem_ball,dist_zero_right] using hp).le
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  let μ := hillScaledDirichletRoot h0q h0r (1/16) k p
  let M := hillLocalGapMidpoint 0 h0q h0r k p
  let Y := hillComplexDirichletGapTerminal h0q h0r k p
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  obtain ⟨hb,a,ha,b,hb',haz,hbz,horders⟩ := hpairs p hpB k hkp
  have haB : a ∈ ball c R := ball_subset_ball (by linarith : (1/16)*R≤R) ha
  have hbB : b ∈ ball c R := ball_subset_ball (by linarith : (1/16)*R≤R) hb'
  have hmid : M=(a+b)/2 := (hillLocalGapSymmetricData_eq_of_pair 0 h0q h0r k hk1 p hb haB hbB horders).1
  have had : ‖a-c‖≤R/16 := by
    have hh : ‖a-c‖<(1/16)*R := by simpa only [mem_ball,dist_eq_norm] using ha
    linarith
  have hbd : ‖b-c‖≤R/16 := by
    have hh : ‖b-c‖<(1/16)*R := by simpa only [mem_ball,dist_eq_norm] using hb'
    linarith
  have hmd : ‖M-c‖≤R/16 := by
    rw [hmid,show (a+b)/2-c=((a-c)+(b-c))/2 by ring,norm_div]
    norm_num only [norm_ofNat]
    have hh := norm_add_le (a-c) (b-c)
    linarith
  have hμd : ‖μ-c‖≤R/16 := by
    have hh : ‖μ-c‖<(1/16)*R := by simpa only [mem_ball,dist_eq_norm] using ((hd k hkd).2 p hpB).1
    linarith
  have hdif : ‖M-μ‖≤R/8 := by
    have hh := norm_sub_le_norm_sub_add_norm_sub M c μ
    rw [norm_sub_rev c μ] at hh
    linarith
  have hY : ‖Y‖≤R/8 := ((ht k hkt).2 p hp).2
  have hsq : Y^2=(μ-M)^2-hillLocalGapSquare 0 h0q h0r k p/4 := ((ht k hkt).2 p hp).1
  refine ⟨?_,?_,?_⟩
  · change (M-μ+Y)*(M-μ-Y)=_
    linear_combination -hsq
  · change ‖M-μ+Y‖≤R/4
    exact (norm_add_le _ _).trans (by linarith)
  · change ‖M-μ-Y‖≤R/4
    exact (norm_sub_le _ _).trans (by linarith)

end NLS.KdV
