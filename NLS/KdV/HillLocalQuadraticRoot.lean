import NLS.KdV.HillComplexGapQuadraticRoot
import NLS.KdV.HillLocalFreeGapPairs
/-! # Local normalized quadratic-root charts near the free potential

For each fixed positive gap, arbitrary-fraction actual pair confinement
gives the same literal root chart on a complex source neighborhood of zero.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFreeGap_local_quadratic_ratio
    (k : ℕ) (hk : 1 ≤ k) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ V : Set (Coeff 2), IsOpen V ∧ (0 : Coeff 2) ∈ V ∧ ∀ p ∈ V,
      ∀ E : ℂ, ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) ≤
        ‖E-(hillRealGapCenter 0 h0q h0r k : ℂ)‖ →
        ‖hillLocalGapPolynomial 0 h0q h0r k p E/(E-(hillRealGapCenter 0 h0q h0r k : ℂ))^2-1‖ ≤ 17/64 := by
  obtain ⟨V,hV,h0V,hpairs⟩ := exists_hillFreeGap_localized_pairs_neighborhood h0q h0r k hk (ρ/8) (by positivity)
  refine ⟨V,hV,h0V,?_⟩
  intro p hp E hE
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk).1
    (hillRealGapContour_geometry 0 h0q h0r k hk).2.1
  obtain ⟨hboundary,a,ha,b,hb,haz,hbz,hm⟩ := hpairs p hp
  have haB : a ∈ ball c R := ball_subset_ball (by nlinarith : (ρ/8)*R ≤ R) ha
  have hbB : b ∈ ball c R := ball_subset_ball (by nlinarith : (ρ/8)*R ≤ R) hb
  have ha' : ‖a-c‖ ≤ (1/8)*‖E-c‖ := by
    have hh : ‖a-c‖ < (ρ/8)*R := by simpa only [mem_ball,dist_eq_norm] using ha
    linarith
  have hb' : ‖b-c‖ ≤ (1/8)*‖E-c‖ := by
    have hh : ‖b-c‖ < (ρ/8)*R := by simpa only [mem_ball,dist_eq_norm] using hb
    linarith
  rw [hillLocalGapPolynomial_eq_of_pair 0 h0q h0r k hk p hboundary haB hbB hm]
  have h := norm_two_root_factor_div_center_sq_sub_one_le a b c E ‖E-c‖ (1/8)
    ((mul_pos hρ hR).trans_le hE : 0 < ‖E-c‖) (by norm_num) ha' hb' rfl
  norm_num at h ⊢
  exact h

theorem exists_hillFreeGap_local_quadratic_root_chart
    (k : ℕ) (hk : 1 ≤ k) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ V : Set (Coeff 2), IsOpen V ∧ (0 : Coeff 2) ∈ V ∧
      AnalyticOnNhd ℂ (hillFreeGapQuadraticRoot h0q h0r k)
        ({E : ℂ | ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) ≤
          ‖E-(hillRealGapCenter 0 h0q h0r k : ℂ)‖} ×ˢ V) ∧
      ∀ p ∈ V, ∀ E : ℂ,
        ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) ≤
          ‖E-(hillRealGapCenter 0 h0q h0r k : ℂ)‖ →
        hillFreeGapQuadraticRoot h0q h0r k (E,p)^2=hillLocalGapPolynomial 0 h0q h0r k p E ∧
        hillFreeGapQuadraticRoot h0q h0r k (E,p)≠0 ∧
        ‖E-(hillRealGapCenter 0 h0q h0r k : ℂ)‖/2 ≤ ‖hillFreeGapQuadraticRoot h0q h0r k (E,p)‖ ∧
        ‖hillFreeGapQuadraticRoot h0q h0r k (E,p)‖ ≤ 2*‖E-(hillRealGapCenter 0 h0q h0r k : ℂ)‖ := by
  obtain ⟨Vr,hVr,h0Vr,hratio⟩ := exists_hillFreeGap_local_quadratic_ratio h0q h0r k hk ρ hρ hρ1
  obtain ⟨Vs,hVs,h0Vs,hM,hS,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood 0 h0q h0r k hk
  let V := Vr ∩ Vs
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk).1
    (hillRealGapContour_geometry 0 h0q h0r k hk).2.1
  have hEc (E : ℂ) (hE : ρ*R ≤ ‖E-c‖) : E-c≠0 := norm_pos_iff.mp ((mul_pos hρ hR).trans_le hE)
  have hP : AnalyticOnNhd ℂ (fun t : ℂ × Coeff 2 => hillLocalGapPolynomial 0 h0q h0r k t.2 t.1)
      (univ ×ˢ V) := by
    intro t ht
    exact ((analyticAt_fst.sub ((hM t.2 ht.2.2).comp analyticAt_snd)).pow 2).sub
      (((hS t.2 ht.2.2).comp analyticAt_snd).div_const)
  refine ⟨V,hVr.inter hVs,⟨h0Vr,by simpa only [map_zero] using h0Vs⟩,?_,?_⟩
  · intro t ht
    have hf : AnalyticAt ℂ (fun u : ℂ × Coeff 2 => u.1-c) t := analyticAt_fst.sub analyticAt_const
    have hrat := (hP t ⟨mem_univ _,ht.2⟩).div (hf.pow 2) (pow_ne_zero 2 (hEc t.1 ht.1))
    have hsmall := hratio t.2 ht.2.1 t.1 ht.1
    have hs := Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds
      (mem_slitPlane_of_norm_sub_one_le_half _ (hsmall.trans (by norm_num))))
    have hfc : AnalyticAt ℂ (fun u : ℂ × Coeff 2 => c-u.1) t := analyticAt_const.sub analyticAt_fst
    exact hfc.mul (hs.comp (f := fun u : ℂ × Coeff 2 => hillLocalGapPolynomial 0 h0q h0r k u.2 u.1/(u.1-c)^2) hrat)
  · intro p hp E hE
    have hsmall := hratio p hp.1 E hE
    have hclose := (norm_sqrt_sub_one_le _).trans hsmall
    have hlo : 1/2 ≤ ‖sqrt (hillLocalGapPolynomial 0 h0q h0r k p E/(E-c)^2)‖ := by
      have hh := norm_sub_norm_le (1 : ℂ) (sqrt (hillLocalGapPolynomial 0 h0q h0r k p E/(E-c)^2))
      rw [norm_one,norm_sub_rev] at hh
      linarith
    have hup : ‖sqrt (hillLocalGapPolynomial 0 h0q h0r k p E/(E-c)^2)‖ ≤ 2 := by
      have hh := norm_le_norm_sub_add (sqrt (hillLocalGapPolynomial 0 h0q h0r k p E/(E-c)^2)) 1
      rw [norm_one] at hh
      linarith
    refine ⟨?_,?_,?_,?_⟩
    · rw [hillFreeGapQuadraticRoot,mul_pow,complex_sqrt_sq,show (c-E)^2=(E-c)^2 by ring]
      exact mul_div_cancel₀ _ (pow_ne_zero 2 (hEc E hE))
    · exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp (hEc E hE)))) (norm_pos_iff.mp (by linarith))
    · change ‖E-c‖/2 ≤ ‖(c-E)*sqrt (hillLocalGapPolynomial 0 h0q h0r k p E/(E-c)^2)‖
      rw [norm_mul,norm_sub_rev c E]
      nlinarith [mul_le_mul_of_nonneg_left hlo (norm_nonneg (E-c))]
    · change ‖(c-E)*sqrt (hillLocalGapPolynomial 0 h0q h0r k p E/(E-c)^2)‖ ≤ 2*‖E-c‖
      rw [norm_mul,norm_sub_rev c E]
      nlinarith [mul_le_mul_of_nonneg_left hup (norm_nonneg (E-c))]

end NLS.KdV
