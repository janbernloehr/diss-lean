import NLS.KdV.HillUniformComplexDeflatedTraceBounds
import NLS.KdV.HillCommonComplexActionGapRatio
import NLS.ComplexAnalysis.QuadraticGapActionRatioBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillComplexActionGapRatio_uniform_inverse_index_bound :
    ∃ C : ℝ, 0<C ∧ ∀ B : ℝ, ∃ N : ℕ, 1≤N ∧ ∀ p : Coeff 2, ‖p‖≤B →
      ∀ k : ℕ, N≤k → ‖hillComplexActionGapRatio h0q h0r k p‖≤C/(k:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := exists_hillComplexDeflatedTraceNumerator_uniform_half_disc_bound h0q h0r
  refine ⟨64*C/Real.pi^2,by positivity,?_⟩
  intro B
  obtain ⟨Nb,hNb,hb⟩ := hbound B
  obtain ⟨Na,hNa,ha⟩ := exists_hillComplexDeflatedTraceNumerator_common_analytic h0q h0r (B+1)
  obtain ⟨Nl,hNl,hl⟩ := exists_hillFreeGap_bounded_complex_midpoint_halfgap_localization h0q h0r (1/16) (by norm_num) (by norm_num) B
  refine ⟨Nb+Na+Nl,hNb.trans (by omega),?_⟩
  intro p hp k hk
  have hkb : Nb≤k := by omega
  have hka : Na≤k := by omega
  have hkl : Nl≤k := by omega
  have hk1 := hNb.trans hkb
  have hkpos : 0<(k:ℝ) := by exact_mod_cast (show 0<k by omega)
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  let M := hillLocalGapMidpoint 0 h0q h0r k p
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hpB : p∈ball (0 : Coeff 2) (B+1) := by rw [mem_ball,dist_zero_right];linarith
  obtain ⟨hM,hS⟩ := hl p hp k hkl
  have hsub : closedBall M (R/4)⊆closedBall c (R/2) := by
    intro E hE
    have hE' : ‖E-M‖≤R/4 := by simpa only [mem_closedBall,dist_eq_norm] using hE
    have htri := norm_sub_le_norm_sub_add_norm_sub E M c
    rw [mem_closedBall,dist_eq_norm]
    dsimp only [M,c,R] at *
    linarith
  have hsub' : closedBall M (R/4)⊆closedBall c R :=
    hsub.trans (closedBall_subset_closedBall (by linarith : R/2≤R))
  have han : AnalyticOnNhd ℂ (fun E => hillComplexDeflatedTraceNumerator h0q h0r k (E,p)) (closedBall M (R/4)) := by
    intro E hE
    exact (ha k hka (E,p) ⟨hsub' hE,hpB⟩).comp
      (f := fun z : ℂ => (z,p)) (analyticAt_id.prod analyticAt_const)
  have hratio := norm_quadraticGapActionRatio_le_of_disc_bound
    (hillComplexDeflatedTraceNumerator h0q h0r k) (hillLocalGapMidpoint 0 h0q h0r k)
    (fun a => hillLocalGapSquare 0 h0q h0r k a/4) p (R/4) C (by positivity) hC.le
    (by dsimp only [R] at *;linarith) han (fun E hE => hb p hp k hkb E (hsub hE))
  have hRlow : Real.pi^2*(k:ℝ)/4≤R := by
    dsimp only [R]
    rw [hillFreeGapHalfLength h0q h0r k hk1,hillFreeGapCollar h0q h0r k hk1,zero_add]
    have hh : (1:ℝ)≤k := by exact_mod_cast hk1
    nlinarith [sq_pos_of_pos Real.pi_pos]
  calc
    ‖hillComplexActionGapRatio h0q h0r k p‖≤4*C/(R/4) := hratio
    _ = 16*C/R := by field_simp;ring
    _ ≤ 16*C/(Real.pi^2*(k:ℝ)/4) := div_le_div_of_nonneg_left (by positivity) (by positivity) hRlow
    _ = (64*C/Real.pi^2)/(k:ℝ) := by field_simp;ring

end NLS.KdV
