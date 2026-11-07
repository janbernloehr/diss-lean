import NLS.Articles.KdVPseudomeasures.SourceThreshold36StripBounds
import NLS.KdV.WideStripCouplingCauchy
import NLS.ComplexAnalysis.CoupledRatioBounds

/-! The genuinely complex physical coupling/gap comparison: both
squared constants follow from the printed modulus ratio and threshold (36). -/
noncomputable section
open Set Metric NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem source_complex_coupling_gap_comparison (r : ℝ) (hr : 0≤r) (hr1 : r<1/2)
    (C m : ℝ) (hC : sourceCoefficientConstant r≤C) (hm : 1≤m)
    (n : ℕ) (hn : 2≤n) (h36 : 8*C/(n:ℝ)^(1/2-r)≤1/(16*m))
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (hq : ‖q‖≤m) (hq0 : q.val 0=0)
    (p : EndpointHillComplexPair r hr hr1 q n) :
    let α := endpointHillDiagonalRoot r hr hr1 n (by omega) q
    endpointLowerCoupling r hr hr1 n (q,α)≠0 →
    (1:ℝ)/9≤‖endpointUpperCoupling r hr hr1 n (q,α)/endpointLowerCoupling r hr hr1 n (q,α)‖ →
    ‖endpointUpperCoupling r hr hr1 n (q,α)/endpointLowerCoupling r hr hr1 n (q,α)‖≤9 →
    ‖endpointUpperCoupling r hr hr1 n (q,α)*endpointLowerCoupling r hr hr1 n (q,α)‖≤‖p.right-p.left‖^2 ∧
    ‖p.right-p.left‖^2≤9*‖endpointUpperCoupling r hr hr1 n (q,α)*endpointLowerCoupling r hr hr1 n (q,α)‖ := by
  dsimp only
  intro hcne hratioLow hratioHigh
  let α := endpointHillDiagonalRoot r hr hr1 n (by omega) q
  let a := fun z : ℂ => endpointDiagonal r hr hr1 n (q,z)
  let b := fun z : ℂ => endpointUpperCoupling r hr hr1 n (q,z)
  let c := fun z : ℂ => endpointLowerCoupling r hr hr1 n (q,z)
  let F := fun z : ℂ => endpointReducedDeterminant r hr hr1 n (q,z)
  change c α≠0 at hcne
  change (1:ℝ)/9≤‖b α/c α‖ at hratioLow
  change ‖b α/c α‖≤9 at hratioHigh
  let u := Complex.sqrt (b α*c α)
  obtain ⟨hu,hu₂,hb₀,hc₀⟩ := coupled_sqrt_bounds_of_ratio (b α) (c α) hcne hratioLow hratioHigh
  have hn1 : 1≤n := by omega
  have hwide := source_threshold36_wide_small r hr1 C m hC hm n hn h36 q hq
  have hs := endpointHill_small_of_wide_small r hr1 n q hwide
  have hαspec := endpointHillDiagonalRoot_spec r hr hr1 n hn1 q hs
  have hαwide : α ∈ wideHillStrip n := reducedHillStrip_subset_wide n hαspec.1
  have hmScaled := source_threshold36_scaled_m r C m hr
    ((sourceCoefficientConstant_two_le r hr1).trans hC) hm n hn1 h36
  have hαm := source_threshold36_root_bound r hr hr1 C m hC hm n hn h36 q hq hq0
  have hS0 := Real.sqrt_nonneg (n:ℝ)
  have hα : ‖α-(freeHillValue n:ℂ)‖≤Real.sqrt (n:ℝ)/256 := by
    change ‖endpointHillDiagonalRoot r hr hr1 n hn1 q-(freeHillValue n:ℂ)‖≤_
    linarith [hmScaled.2]
  have hbc := source_threshold36_coupling_bounds r hr hr1 C m hC hm n hn h36 q hq α hαwide
  have hnorm : ‖u‖^2=‖b α*c α‖ := by
    simpa only [norm_pow] using congrArg norm hu₂
  have hρ : ‖u‖≤Real.sqrt (n:ℝ)/32 := by
    apply (sq_le_sq₀ (norm_nonneg u) (by positivity : (0:ℝ)≤Real.sqrt (n:ℝ)/32)).mp
    rw [hnorm,norm_mul,pow_two]
    exact mul_le_mul hbc.1 hbc.2 (norm_nonneg _) (by positivity)
  have hAB (z : ℂ) (hz : z ∈ wideHillStrip n) : ‖a z‖≤Real.sqrt (n:ℝ)/32 := by
    have hh := source_threshold36_diagonal_bound r hr hr1 C m hC hm n hn h36 q hq hq0 z hz
    change ‖endpointDiagonal r hr hr1 n (q,z)‖≤_
    linarith [hmScaled.2]
  have hBB (z : ℂ) (hz : z ∈ wideHillStrip n) : ‖b z‖≤Real.sqrt (n:ℝ)/32 :=
    (source_threshold36_coupling_bounds r hr hr1 C m hC hm n hn h36 q hq z hz).1
  have hCB (z : ℂ) (hz : z ∈ wideHillStrip n) : ‖c z‖≤Real.sqrt (n:ℝ)/32 :=
    (source_threshold36_coupling_bounds r hr hr1 C m hC hm n hn h36 q hq z hz).2
  have hA (z : ℂ) (hz : z ∈ wideHillStrip n) : AnalyticAt ℂ a z ∧ AnalyticAt ℂ b z ∧ AnalyticAt ℂ c z := by
    obtain ⟨ha,hb,hc⟩ := analyticAt_endpointCoefficients_wide r hr hr1 n hn (q,z) hz hwide
    exact ⟨ha.comp (analyticAt_const.prod analyticAt_id),hb.comp (analyticAt_const.prod analyticAt_id),
      hc.comp (analyticAt_const.prod analyticAt_id)⟩
  have hdisc : closedBall α (2*‖u‖)⊆reducedHillStrip n := by
    intro z hz
    apply endpointHillDisc_subset_strip n hn1
    rw [mem_closedBall,dist_eq_norm]
    have hd : ‖z-α‖≤2*‖u‖ := by simpa only [mem_closedBall,dist_eq_norm] using hz
    have ht := norm_sub_le_norm_sub_add_norm_sub z α (freeHillValue n:ℂ)
    linarith
  have hvarA := wideStrip_smallDisc_variation n hn1 α ‖u‖ (norm_nonneg u) hα hρ a
    (fun z hz => (hA z hz).1) hAB
  have hvarB := wideStrip_smallDisc_variation n hn1 α ‖u‖ (norm_nonneg u) hα hρ b
    (fun z hz => (hA z hz).2.1) hBB
  have hvarC := wideStrip_smallDisc_variation n hn1 α ‖u‖ (norm_nonneg u) hα hρ c
    (fun z hz => (hA z hz).2.2) hCB
  have hfactor (z : ℂ) (hz : z ∈ closedBall α (2*‖u‖)) :
      F z=(z-α-(a z-a α))^2-b z*c z := by
    have he : z-(freeHillValue n:ℂ)-a z=z-α-(a z-a α) := by
      dsimp [a,α]
      linear_combination hαspec.2.1
    calc
      F z=(z-(freeHillValue n:ℂ)-a z)^2-b z*c z :=
        endpointReducedDeterminant_factorization r hr hr1 n hn1 q hs z (hdisc hz)
      _ = _ := by rw [he]
  have hF : AnalyticOnNhd ℂ F (closedBall α (2*‖u‖)) :=
    (analyticOnNhd_endpointReducedDeterminant_spectral r hr hr1 n hn1 q hs).mono hdisc
  obtain ⟨x,hx,y,hy,hFx,hFy,hlo,hhi⟩ := coupledQuadratic_isolated_roots F (fun z => a z-a α) b c
    α u (b α) (c α) hu hu₂ hF hfactor hb₀ hc₀ (fun z hz => ⟨hvarA z hz,hvarB z hz,hvarC z hz⟩)
  have hxdisc := coupledRootDisc_subset α u hx
  have hy' : y ∈ closedBall (α+ -u) (‖-u‖/2) := by simpa only [norm_neg,sub_eq_add_neg] using hy
  have hydisc : y ∈ closedBall α (2*‖u‖) := by
    simpa only [norm_neg] using coupledRootDisc_subset α (-u) hy'
  have hxNative := hdisc hxdisc
  have hyNative := hdisc hydisc
  have hxChoice := (p.spectrum_iff x hxNative).mp
    ((mem_endpointHillSpectrum_iff_determinant r hr hr1 n hn1 x hxNative q hs).mpr hFx)
  have hyChoice := (p.spectrum_iff y hyNative).mp
    ((mem_endpointHillSpectrum_iff_determinant r hr hr1 n hn1 y hyNative q hs).mpr hFy)
  have hxy : x≠y := by
    intro he
    rw [he,sub_self,norm_zero] at hlo
    exact (norm_pos_iff.mpr hu).not_ge hlo
  have hgap : ‖p.right-p.left‖=‖x-y‖ := by
    rcases hxChoice with hxL | hxR <;> rcases hyChoice with hyL | hyR
    · exact (hxy (hxL.trans hyL.symm)).elim
    · rw [hxL,hyR,norm_sub_rev]
    · rw [hxR,hyL]
    · exact (hxy (hxR.trans hyR.symm)).elim
  change ‖b α*c α‖≤‖p.right-p.left‖^2 ∧ ‖p.right-p.left‖^2≤9*‖b α*c α‖
  rw [hgap,← hnorm]
  constructor <;> nlinarith [norm_nonneg (x-y),norm_nonneg u]

end NLS.Articles.KdVPseudomeasures
