import NLS.KdV.HillHminusOneCumulativeCounts

/-! # H^-1 continuity of every intrinsic real characteristic label

A single local central cutoff contains a prescribed label. Diameter-disc
counts stabilize by joint continuity of the actual entire characteristic.
Finite ordered count stability then includes closed gaps and repeated
central roots, without a simple-root hypothesis or a bounded L2 norm.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped Classical
namespace NLS.KdV

theorem HillHminusRealCharacteristicLabeling.ne_zero_of_not_central_value
    {q : PeriodOneHminusOne} {N : ℕ} {r : ℝ} {lambda : ℕ → ℝ}
    (h : HillHminusRealCharacteristicLabeling q N r lambda)
    (c : ℝ) (hc : c < hillCentralSeparator N)
    (hnot : c ∉ (Finset.range (2*N-1)).image lambda) : hillHminusRadicand q c ≠ 0 := by
  intro hd
  obtain ⟨j,hj⟩ := (h.roots c).mp hd
  have he : lambda j = c := (ofReal_injective hj).symm
  by_cases hjl : j < 2*N-1
  · exact hnot (Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr hjl,he⟩)
  · have hh := h.tail_above_separator j (by omega)
    rw [he] at hh
    linarith

theorem continuousAt_hillHminusRealLabels_family
    {T : Type*} [TopologicalSpace T]
    (Q : T → PeriodOneHminusOne) (hQ : Continuous Q)
    (hreal : ∀ t, IsRealPeriodOneHminusOne (Q t)) (t0 : T) (j : ℕ) :
    ContinuousAt (fun t => hillHminusRealLabels (Q t) (hreal t) j) t0 := by
  obtain ⟨N,r,V,hjN,hN,hV,hqV,hspec⟩ := exists_hillHminusRealLabels_common_spec (Q t0) (j+2)
  have hj : j < 2*N-1 := by omega
  have hevent : ∀ᶠ t in 𝓝 t0, Q t ∈ V :=
    hQ.continuousAt.preimage_mem_nhds (hV.mem_nhds hqV)
  let labels (t : T) := hillHminusRealLabels (Q t) (hreal t)
  have hs0 := hspec (Q t0) hqV (hreal t0)
  let F : T → ℂ → ℂ := fun t z => hillHminusRadicand (Q t) z
  have hF : Continuous F.uncurry := by
    have hc : Continuous (fun p : ℂ × PeriodOneHminusOne => hillHminusRadicand p.2 p.1) :=
      analyticOnNhd_hillHminusRadicand_joint.continuous
    have hm : Continuous (fun p : T × ℂ => (p.2,Q p.1)) :=
      continuous_snd.prodMk (hQ.comp continuous_fst)
    exact Continuous.comp (g := fun p : ℂ × PeriodOneHminusOne => hillHminusRadicand p.2 p.1)
      (f := fun p : T × ℂ => (p.2,Q p.1)) hc hm
  apply NLS.tendsto_ordered_finite_of_counts (2*N-1) labels (labels t0)
    (-(N : ℝ)^2) (hillCentralSeparator N)
    (fun t i _ k _ hik => monotone_hillHminusRealLabels (Q t) (hreal t) hik)
    (fun i _ k _ hik => hs0.monotone hik) hs0.central_mem ?_ j hj
  intro c hc hnot
  have hnc := hs0.ne_zero_of_not_central_value c hc.2 hnot
  have hr : 0 < (c-(-(N : ℝ)^2))/2 := by linarith [hc.1]
  have hb : ∀ z ∈ sphere (((-(N : ℝ)^2+c)/2 : ℝ) : ℂ) ((c-(-(N : ℝ)^2))/2), F t0 z ≠ 0 := by
    apply NLS.ComplexAnalysis.ne_zero_on_realDiameter_sphere
      (hillHminusRadicand (Q t0)) (-(N : ℝ)^2) c hc.1.le
      (fun z hz => hillHminusRadicand_root_im_zero _ (hreal t0) z hz) ?_ hnc
    intro hd
    have hh := hs0.central_control.root_lower _ hd
    exact lt_irrefl _ hh
  have hstable := NLS.ComplexAnalysis.eventually_analyticZeroCount_eq_of_continuous_family F
    (((-(N : ℝ)^2+c)/2 : ℝ) : ℂ) ((c-(-(N : ℝ)^2))/2) hr hF.continuousOn
    (fun t => (analyticOnNhd_hillHminusRadicand (Q t)).mono (subset_univ _)) t0 hb
  filter_upwards [hstable,hevent] with t ht hct
  have hs := hspec (Q t) hct (hreal t)
  have hc0 := hs0.cumulative_count (hreal t0) c hc.2.le
  have hct' := hs.cumulative_count (hreal t) c hc.2.le
  exact hct'.symm.trans (ht.trans hc0)

theorem continuous_hillHminusRealLabels_family
    {T : Type*} [TopologicalSpace T]
    (Q : T → PeriodOneHminusOne) (hQ : Continuous Q)
    (hreal : ∀ t, IsRealPeriodOneHminusOne (Q t)) (j : ℕ) :
    Continuous (fun t => hillHminusRealLabels (Q t) (hreal t) j) :=
  continuous_iff_continuousAt.mpr (fun t => continuousAt_hillHminusRealLabels_family Q hQ hreal t j)

theorem continuous_hillHminusRealLabels (j : ℕ) :
    Continuous (fun q : PeriodOneRealHminusOne => hillHminusRealLabels q.val q.property j) :=
  continuous_hillHminusRealLabels_family Subtype.val continuous_subtype_val (fun q => q.property) j

theorem continuous_hillHminusLowestRealRoot :
    Continuous (fun q : PeriodOneRealHminusOne => hillHminusLowestRealRoot q.val q.property) := by
  simpa only [hillHminusRealLabels_zero_eq_lowest] using continuous_hillHminusRealLabels 0

end NLS.KdV
