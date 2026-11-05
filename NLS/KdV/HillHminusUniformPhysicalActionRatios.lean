import NLS.KdV.HillHminusCommonPhysicalActions
import NLS.KdV.HillHminusActionRatioGermIdentification

/-! # A common rough neighborhood for every high physical action ratio

The actual contour action supplies the physical action identity. Analytic
cancellation through the collapsed free gap then identifies the ratio on
its entire rough ball, including physical sources with large L2 norm.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.KdV
variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
theorem exists_hillHminus_high_physical_action_ratios :
    ∃ η : ℝ, ∃ N : ℕ, 0 < η ∧ 2 ≤ N ∧ ∀ n : ℕ+, N ≤ (n : ℕ) →
      ∃ R : PeriodOneHminusOne → ℂ,
        AnalyticOnNhd ℂ R (ball (0 : PeriodOneHminusOne) η) ∧
        (∀ q ∈ ball (0 : PeriodOneHminusOne) η, ‖R q‖ ≤ 2/(n : ℝ) ∧ 0 < (R q).re) ∧
        ∀ p : RealPeriodOneHillPotential,
          (hillPhysicalHminusEmbedding p).val ∈ ball (0 : PeriodOneHminusOne) η →
          R (hillPhysicalHminusEmbedding p).val =
            hillActionGapRatio p.val p.property.1 p.property.2 (n : ℕ) := by
  let p0 : RealPeriodOneHillPotential := ⟨0,h0q,h0r⟩
  obtain ⟨r,_hr,_hrpi,hfamily⟩ := exists_hillOriginal_high_actions_common_hminus_extension p0
  obtain ⟨N,V,W,hN,hV,h0V,hW,h0W,hfamily⟩ := hfamily (1/2) (by norm_num)
  have hzero : hillOriginalHminusSource p0.val=0 := map_zero _
  rw [hzero] at h0V
  obtain ⟨η,hη,hsub⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds h0V)
  refine ⟨η,N,hη,hN,?_⟩
  intro n hn
  obtain ⟨A,F,_hAa,hFa,hproperties,hphysical⟩ := hfamily n hn
  let d : ℝ := 2*Real.pi*(n : ℝ)
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdc : (d : ℂ)=2*((Real.pi : ℂ)*(n : ℕ)) := by dsimp only [d]; push_cast; ring
  let R : PeriodOneHminusOne → ℂ := fun q => F q/(d : ℂ)
  have hRa : AnalyticOnNhd ℂ R (ball (0 : PeriodOneHminusOne) η) :=
    (hFa.mono hsub).div_const
  have ht : Tendsto (fun p : RealPeriodOneHillPotential => hillOriginalHminusSource p.val)
      (𝓝 p0) (𝓝 (0 : PeriodOneHminusOne)) := by
    simpa only [Function.comp_def,p0,map_zero] using
      (hillOriginalHminusSource.continuous.comp continuous_subtype_val).tendsto p0
  have haction : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 p0,
      (hillRealGapIntegral p.val p.property.1 p.property.2 (n : ℕ) 0 : ℂ)=
        (hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ) : ℂ)^2*
          R (hillPhysicalHminusEmbedding p).val := by
    filter_upwards [hW.mem_nhds h0W,ht.eventually (hV.mem_nhds h0V)] with p hpW hpV
    rw [← (hphysical p hpW).1,(hproperties _ hpV).2.2,(hphysical p hpW).2]
    rw [← hdc]
    change _=(hillRealGapHalfLength p.val p.property.1 p.property.2 (n : ℕ) : ℂ)^2*
      (F (hillOriginalHminusSource p.val)/(d : ℂ))
    ring
  refine ⟨R,hRa,?_,?_⟩
  · intro q hq
    have hnear := (hproperties q (hsub hq)).1
    have hFnorm : ‖F q‖ ≤ 2 := by
      have hh := norm_le_norm_sub_add (F q) (1 : ℂ)
      rw [norm_one] at hh
      linarith
    have hFpos : 0 < (F q).re := by
      have hh : 1-(F q).re ≤ ‖F q-1‖ := by
        rw [norm_sub_rev]
        simpa only [sub_re,one_re] using re_le_norm (1-F q)
      linarith
    constructor
    · change ‖F q/(d : ℂ)‖ ≤ _
      rw [norm_div,norm_real,Real.norm_of_nonneg hd.le]
      have hnpos : 0 < (n : ℝ) := by positivity
      have hnd : (n : ℝ) ≤ d := by
        have hpi := Real.pi_gt_three
        have hh := mul_nonneg (show 0 ≤ 2*Real.pi-1 by linarith) hnpos.le
        dsimp only [d]
        nlinarith
      exact (div_le_div_of_nonneg_right hFnorm hd.le).trans
        (div_le_div_of_nonneg_left (by norm_num) hnpos hnd)
    · change 0 < (F q/(d : ℂ)).re
      rw [div_ofReal_re]
      exact div_pos hFpos hd
  · intro p hp
    exact hillHminus_action_ratio_eq_on_ball_of_physical_action_germ h0q h0r η hη n R hRa
      haction p hp

end NLS.KdV
