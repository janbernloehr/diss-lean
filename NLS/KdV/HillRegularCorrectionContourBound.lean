import NLS.KdV.HillGlobalRegularBound

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem norm_hillRegularAbelianCorrection_le_of_contour_bound
    (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) (hkn : k ≠ n) (c : ℂ) (R A : ℝ) (hR : 0 < R) (hA : 0 ≤ A)
    (hfill : closedBall c R ⊆ hillGapFilledDomain q hq hr k)
    (hgap : segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ) ⊆ ball c R)
    (hbound : ∀ z ∈ sphere c R,
      ‖hillAbelianSelectedGlobalPsi q hq hr n hn z/hillEnergyCanonicalRootProduct q hq hr z‖ ≤ A) :
    ‖hillRegularAbelianCorrection q hq hr n hn k hk‖ ≤ 4*Real.pi*R*A := by
  let a : ℂ := hillRealLabels q hq hr (2*k-1)
  let b : ℂ := hillRealLabels q hq hr (2*k)
  let g : ℂ → ℂ := fun z => -I*hillAbelianSelectedGlobalPsi q hq hr n hn z/hillDeflatedEnergyCanonicalRoot q hq hr k z
  have hg : AnalyticOnNhd ℂ g (closedBall c R) := by
    intro z hz
    exact (analyticAt_const.mul (analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn z (mem_univ _))).div
      (analyticOnNhd_hillDeflatedEnergyCanonicalRoot q hq hr k z (hfill hz))
      (hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk z (hfill hz))
  have ha : a ∈ ball c R := hgap (left_mem_segment ℝ _ _)
  have hb : b ∈ ball c R := hgap (right_mem_segment ℝ _ _)
  have hsphere (z : ℂ) (hz : z ∈ sphere c R) : ‖g z‖ ≤ (2*R)*A := by
    have hnot : z ∉ segment ℝ a b := fun he => (ne_of_lt (hgap he)) hz
    have hroot : ‖endpointRoot a b z‖ ≤ 2*R := by
      have hzc : ‖z-c‖ = R := by simpa only [mem_sphere,dist_eq_norm] using hz
      have hac : ‖c-a‖ ≤ R := by simpa only [mem_ball,dist_eq_norm,norm_sub_rev] using (show dist a c ≤ R from le_of_lt ha)
      have hbc : ‖c-b‖ ≤ R := by simpa only [mem_ball,dist_eq_norm,norm_sub_rev] using (show dist b c ≤ R from le_of_lt hb)
      have hza : ‖z-a‖ ≤ 2*R := (norm_sub_le_norm_sub_add_norm_sub z c a).trans (by rw [hzc];linarith)
      have hzb : ‖z-b‖ ≤ 2*R := (norm_sub_le_norm_sub_add_norm_sub z c b).trans (by rw [hzc];linarith)
      have hs : ‖endpointRoot a b z‖^2 = ‖z-a‖*‖z-b‖ := by rw [← norm_pow,endpointRoot_sq a b z hnot,norm_mul]
      have hp := mul_le_mul hza hzb (norm_nonneg (z-b)) (by positivity : 0 ≤ 2*R)
      nlinarith [norm_nonneg (endpointRoot a b z)]
    have hcut := mem_hillL2RealCutDomain_of_filled_not_gap q hq hr k hk z (hfill (sphere_subset_closedBall hz)) hnot
    have hRn := hillEnergyCanonicalRootProduct_ne_zero_on_realCutDomain q hq hr z hcut
    have hUn := hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk z (hfill (sphere_subset_closedBall hz))
    have hEn := endpointRoot_ne_zero_of_not_mem_segment a b z hnot
    have he : g z = (-I)*(hillAbelianSelectedGlobalPsi q hq hr n hn z/hillEnergyCanonicalRootProduct q hq hr z)*endpointRoot a b z := by
      rw [hillEnergyCanonicalRootProduct_eq_endpoint_mul_deflated q hq hr k hk z]
      dsimp only [g,a,b]
      change endpointRoot (↑(hillRealLabels q hq hr (2*k-1))) (↑(hillRealLabels q hq hr (2*k))) z ≠ 0 at hEn
      field_simp [hEn,hUn]
    rw [he,norm_mul,norm_mul,norm_neg,norm_I,one_mul]
    exact (mul_le_mul (hbound z hz) hroot (norm_nonneg _) hA).trans_eq (by ring)
  have hdisc (z : ℂ) (hz : z ∈ closedBall c R) : ‖g z‖ ≤ (2*R)*A := by
    have hdc : DiffContOnCl ℂ g (ball c R) :=
      DiffContOnCl.mk_ball (hg.differentiableOn.mono ball_subset_closedBall) hg.continuousOn
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc
    · intro w hw
      rw [frontier_ball c hR.ne'] at hw
      exact hsphere w hw
    · rw [closure_ball c hR.ne']
      exact hz
  have h := norm_hillRegularAbelianCorrection_le_of_differential_bound q hq hr n k hn hk ((2*R)*A)
    (by positivity) (fun E hE => by simpa only [if_neg hkn,sub_zero,g] using hdisc E (ball_subset_closedBall (hgap hE)))
  exact h.trans_eq (by ring)

end NLS.KdV
