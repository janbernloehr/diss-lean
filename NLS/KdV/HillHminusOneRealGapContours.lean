import NLS.KdV.HillHminusOneTraceParity
import NLS.ComplexAnalysis.RealGapDiscIsolation

/-! # Intrinsic isolating circles for every real H^-1 Hill gap

The gap midpoint and a quarter of the smaller neighboring band length
give canonical inner and outer circles. No high-index restriction or
positive gap length is required.
-/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped Classical
namespace NLS.KdV
open NLS.ComplexAnalysis

/-- The geometric real-band domain of the actual H^-1 characteristic.
A holomorphic primitive on this whole domain is a separate construction. -/
def hillHminusRealCutDomain (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) : Set ℂ :=
  {z | z.im ≠ 0 ∨ ∃ n : ℕ,
    z.re ∈ Ioo (hillHminusRealLabels q hr (2*n)) (hillHminusRealLabels q hr (2*n+1))}

theorem isOpen_hillHminusRealCutDomain
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) : IsOpen (hillHminusRealCutDomain q hr) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  rcases hz with hne | ⟨n,hn⟩
  · exact Filter.mem_of_superset ((isOpen_ne_fun continuous_im continuous_const).mem_nhds hne)
      (fun w hw => Or.inl hw)
  · exact Filter.mem_of_superset ((isOpen_Ioo.preimage continuous_re).mem_nhds hn)
      (fun w hw => Or.inr ⟨n,hw⟩)

theorem hillHminusRadicand_ne_zero_between_labels
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (j : ℕ) (x : ℝ)
    (hx : x ∈ Ioo (hillHminusRealLabels q hr j) (hillHminusRealLabels q hr (j+1))) :
    hillHminusRadicand q x ≠ 0 := by
  intro hz
  obtain ⟨k,hk⟩ := (hillHminusRealLabels_root_iff q hr (x : ℂ)).mp hz
  have he : x = hillHminusRealLabels q hr k := ofReal_injective hk
  by_cases hkj : k ≤ j
  · have hm := monotone_hillHminusRealLabels q hr hkj
    linarith [hx.1]
  · have hm := monotone_hillHminusRealLabels q hr (show j+1 ≤ k by omega)
    linarith [hx.2]

theorem hillHminusRadicand_ne_zero_on_realCutDomain
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q)
    (z : ℂ) (hz : z ∈ hillHminusRealCutDomain q hr) : hillHminusRadicand q z ≠ 0 := by
  intro hzero
  have hi := hillHminusRadicand_root_im_zero q hr z hzero
  rcases hz with him | ⟨n,hn⟩
  · exact him hi
  · have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
    exact hillHminusRadicand_ne_zero_between_labels q hr (2*n) z.re hn (by rwa [← he])

def hillHminusRealGapCenter
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) : ℝ :=
  (hillHminusRealLabels q hr (2 * n - 1) + hillHminusRealLabels q hr (2 * n)) / 2

def hillHminusRealGapHalfLength
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) : ℝ :=
  (hillHminusRealLabels q hr (2 * n) - hillHminusRealLabels q hr (2 * n - 1)) / 2

def hillHminusRealGapCollar
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) : ℝ :=
  min (hillHminusRealLabels q hr (2 * n - 1) - hillHminusRealLabels q hr (2 * n - 2))
    (hillHminusRealLabels q hr (2 * n + 1) - hillHminusRealLabels q hr (2 * n)) / 4

theorem hillHminusRealGapContour_geometry
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ hillHminusRealGapHalfLength q hr n ∧ 0 < hillHminusRealGapCollar q hr n ∧
      hillHminusRealGapCenter q hr n - hillHminusRealGapHalfLength q hr n = hillHminusRealLabels q hr (2 * n - 1) ∧
      hillHminusRealGapCenter q hr n + hillHminusRealGapHalfLength q hr n = hillHminusRealLabels q hr (2 * n) ∧
      ball (hillHminusRealGapCenter q hr n : ℂ)
          (hillHminusRealGapHalfLength q hr n + 2 * hillHminusRealGapCollar q hr n) \
        segment ℝ (hillHminusRealLabels q hr (2 * n - 1) : ℂ) (hillHminusRealLabels q hr (2 * n)) ⊆
          hillHminusRealCutDomain q hr := by
  let l := hillHminusRealLabels q hr (2 * n - 2)
  let a := hillHminusRealLabels q hr (2 * n - 1)
  let b := hillHminusRealLabels q hr (2 * n)
  let u := hillHminusRealLabels q hr (2 * n + 1)
  have hla : l < a := by
    simpa only [show 2 * (n - 1) = 2 * n - 2 by omega,
      show 2 * n - 2 + 1 = 2 * n - 1 by omega] using hillHminusRealLabels_band_strict q hr (n - 1)
  have hab : a ≤ b := monotone_hillHminusRealLabels q hr (by omega)
  have hbu : b < u := hillHminusRealLabels_band_strict q hr n
  have hmin : 0 < min (a - l) (u - b) := lt_min (by linarith) (by linarith)
  have hcollar : 0 < hillHminusRealGapCollar q hr n := div_pos hmin (by norm_num)
  refine ⟨by dsimp [hillHminusRealGapHalfLength]; linarith, hcollar, ?_, ?_, ?_⟩
  · dsimp [hillHminusRealGapCenter, hillHminusRealGapHalfLength]; ring
  · dsimp [hillHminusRealGapCenter, hillHminusRealGapHalfLength]; ring
  · intro z hz
    have hl : l < hillHminusRealGapCenter q hr n -
        (hillHminusRealGapHalfLength q hr n + 2 * hillHminusRealGapCollar q hr n) := by
      have hm := min_le_left (a - l) (u - b)
      dsimp [hillHminusRealGapCenter, hillHminusRealGapHalfLength, hillHminusRealGapCollar]
      change l < (a + b) / 2 - ((b - a) / 2 + 2 * (min (a - l) (u - b) / 4))
      linarith
    have hu : hillHminusRealGapCenter q hr n +
        (hillHminusRealGapHalfLength q hr n + 2 * hillHminusRealGapCollar q hr n) < u := by
      have hm := min_le_right (a - l) (u - b)
      change (a + b) / 2 + ((b - a) / 2 + 2 * (min (a - l) (u - b) / 4)) < u
      linarith
    rcases real_gap_disc_exterior_band l a b u _ _ hab hl hu z hz with hi | hlband | huband
    · exact Or.inl hi
    · refine Or.inr ⟨n - 1, ?_⟩
      simpa only [show 2 * (n - 1) = 2 * n - 2 by omega,
        show 2 * n - 2 + 1 = 2 * n - 1 by omega] using hlband
    · exact Or.inr ⟨n, huband⟩

theorem hillHminusRealGapContour_sphere_subset
    (q : PeriodOneHminusOne)
    (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) :
    sphere (hillHminusRealGapCenter q hr n : ℂ)
        (hillHminusRealGapHalfLength q hr n + hillHminusRealGapCollar q hr n) ⊆ hillHminusRealCutDomain q hr := by
  obtain ⟨hd, hη, hl, hu, hsub⟩ := hillHminusRealGapContour_geometry q hr n hn
  let c := hillHminusRealGapCenter q hr n
  let d := hillHminusRealGapHalfLength q hr n
  let η := hillHminusRealGapCollar q hr n
  have hcut : segment ℝ (hillHminusRealLabels q hr (2 * n - 1) : ℂ)
      (hillHminusRealLabels q hr (2 * n)) ⊆ ball (c : ℂ) (d + η) := by
    apply (convex_ball _ _).segment_subset
    · rw [← hl]
      simp only [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
      change |c - d - c| < d + η
      rw [show c - d - c = -d by ring, abs_neg, abs_of_nonneg hd]
      linarith
    · rw [← hu]
      simp only [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs]
      change |c + d - c| < d + η
      rw [show c + d - c = d by ring, abs_of_nonneg hd]
      linarith
  intro z hz
  apply hsub
  refine ⟨?_, fun hk => (sphere_disjoint_ball : Disjoint (sphere (c : ℂ) (d + η)) (ball (c : ℂ) (d + η))).le_bot ⟨hz, hcut hk⟩⟩
  rw [mem_ball, mem_sphere.mp hz]
  linarith

/-- The selected gap contains only its two characteristic endpoint
values; at a collapsed gap they are the same value. -/
theorem hillHminusRadicand_zero_on_gap_interval_iff
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (hx : x ∈ Icc (hillHminusRealLabels q hr (2*n-1)) (hillHminusRealLabels q hr (2*n))) :
    hillHminusRadicand q x = 0 ↔
      x = hillHminusRealLabels q hr (2*n-1) ∨ x = hillHminusRealLabels q hr (2*n) := by
  constructor
  · intro hz
    obtain ⟨k,hk⟩ := (hillHminusRealLabels_root_iff q hr (x : ℂ)).mp hz
    have he : x = hillHminusRealLabels q hr k := ofReal_injective hk
    have hprev := hillHminusRealLabels_band_strict q hr (n-1)
    have hpi : 2*(n-1)+1 = 2*n-1 := by omega
    rw [hpi] at hprev
    have hnext := hillHminusRealLabels_band_strict q hr n
    have hklo : 2*n-1 ≤ k := by
      by_contra! hkl
      have hm := monotone_hillHminusRealLabels q hr (show k ≤ 2*(n-1) by omega)
      linarith [hx.1]
    have hkhi : k ≤ 2*n := by
      by_contra! hkh
      have hm := monotone_hillHminusRealLabels q hr (show 2*n+1 ≤ k by omega)
      linarith [hx.2]
    rcases (show k = 2*n-1 ∨ k = 2*n by omega) with rfl | rfl
    · exact Or.inl he
    · exact Or.inr he
  · rintro (rfl | rfl) <;> exact hillHminusRealLabels_root q hr _

/-- The canonical enclosing disc has exactly the actual two gap roots,
counted with analytic multiplicity, for every positive gap index. -/
theorem hillHminusRealGapContour_count_two
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) :
    analyticZeroCount (hillHminusRadicand q)
      (closedBall (hillHminusRealGapCenter q hr n : ℂ)
        (hillHminusRealGapHalfLength q hr n+hillHminusRealGapCollar q hr n)) = 2 := by
  obtain ⟨hd,hη,hl,hu,hsub⟩ := hillHminusRealGapContour_geometry q hr n hn
  let c := hillHminusRealGapCenter q hr n
  let d := hillHminusRealGapHalfLength q hr n
  let η := hillHminusRealGapCollar q hr n
  let l := hillHminusRealLabels q hr (2*n-1)
  let u := hillHminusRealLabels q hr (2*n)
  change c-d = l at hl
  change c+d = u at hu
  have hlmem : (l : ℂ) ∈ closedBall (c : ℂ) (d+η) := by
    rw [← hl,mem_closedBall,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    rw [show c-d-c = -d by ring,abs_neg,abs_of_nonneg hd]
    linarith
  have humem : (u : ℂ) ∈ closedBall (c : ℂ) (d+η) := by
    rw [← hu,mem_closedBall,dist_eq_norm,← ofReal_sub,norm_real,Real.norm_eq_abs]
    rw [show c+d-c = d by ring,abs_of_nonneg hd]
    linarith
  have hzeros (z : ℂ) (hz : z ∈ closedBall (c : ℂ) (d+η)) (hzero : hillHminusRadicand q z = 0) :
      z = (l : ℂ) ∨ z = (u : ℂ) := by
    have hcut : z ∈ segment ℝ (l : ℂ) (u : ℂ) := by
      by_contra hnot
      apply hillHminusRadicand_ne_zero_on_realCutDomain q hr z (hsub ⟨?_,hnot⟩) hzero
      exact closedBall_subset_ball (by linarith : d+η < d+2*η) hz
    have hi := hillHminusRadicand_root_im_zero q hr z hzero
    have he : (z.re : ℂ) = z := by apply Complex.ext <;> simp [hi]
    have hx := re_mem_Icc_of_mem_real_segment l u
      (monotone_hillHminusRealLabels q hr (by omega)) z hcut
    have hp := (hillHminusRadicand_zero_on_gap_interval_iff q hr n hn z.re hx).mp (by rwa [he])
    rcases hp with hp | hp
    · exact Or.inl (he.symm.trans (congrArg ofReal hp))
    · exact Or.inr (he.symm.trans (congrArg ofReal hp))
  rw [analyticZeroCount_eq_sum {(l : ℂ),(u : ℂ)} (by
    intro z hz
    simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption) (by
    intro z hz
    simpa only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] using hzeros z hz.1 hz.2)]
  by_cases he : l = u
  · have ho := hillHminusRealLabels_closed_gap_order q hr n hn he
    change analyticOrderNatAt (hillHminusRadicand q) (l : ℂ) = 2 at ho
    rw [he] at ho
    simpa [he] using ho
  · have ho := hillHminusRealLabels_open_gap_orders q hr n hn he
    have hne : (l : ℂ) ≠ (u : ℂ) := fun h => he (ofReal_injective h)
    rw [Finset.sum_pair hne,ho.1,ho.2]

/-- Every fixed canonical real-gap circle keeps its exact two-root count
and boundary nonvanishing on a complex H^-1 neighborhood. -/
theorem exists_hillHminusRealGapContour_complex_neighborhood
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (n : ℕ) (hn : 1 ≤ n) :
    ∃ V : Set PeriodOneHminusOne, IsOpen V ∧ q ∈ V ∧ ∀ a ∈ V,
      analyticZeroCount (hillHminusRadicand a)
        (closedBall (hillHminusRealGapCenter q hr n : ℂ)
          (hillHminusRealGapHalfLength q hr n+hillHminusRealGapCollar q hr n)) = 2 ∧
      ∀ z ∈ sphere (hillHminusRealGapCenter q hr n : ℂ)
          (hillHminusRealGapHalfLength q hr n+hillHminusRealGapCollar q hr n),
        hillHminusRadicand a z ≠ 0 := by
  let c : ℂ := hillHminusRealGapCenter q hr n
  let R : ℝ := hillHminusRealGapHalfLength q hr n+hillHminusRealGapCollar q hr n
  obtain ⟨hd,hη,_,_,_⟩ := hillHminusRealGapContour_geometry q hr n hn
  have hR : 0 < R := by dsimp only [R]; linarith
  let F : PeriodOneHminusOne → ℂ → ℂ := fun a z => hillHminusRadicand a z
  have hF : Continuous F.uncurry := by
    exact Continuous.comp (g := fun p : ℂ × PeriodOneHminusOne => hillHminusRadicand p.2 p.1)
      (f := fun p : PeriodOneHminusOne × ℂ => (p.2,p.1))
      analyticOnNhd_hillHminusRadicand_joint.continuous (continuous_snd.prodMk continuous_fst)
  have hb (z : ℂ) (hz : z ∈ sphere c R) : F q z ≠ 0 :=
    hillHminusRadicand_ne_zero_on_realCutDomain q hr z (hillHminusRealGapContour_sphere_subset q hr n hn hz)
  have hcount := eventually_analyticZeroCount_eq_of_continuous_family F c R hR hF.continuousOn
    (fun a => (analyticOnNhd_hillHminusRadicand a).mono (subset_univ _)) q hb
  obtain ⟨δ,hδ,hbound⟩ := (isCompact_sphere c R).exists_forall_le'
    (((analyticOnNhd_hillHminusRadicand q).continuousOn.mono (subset_univ _)).norm)
    (fun z hz => norm_pos_iff.mpr (hb z hz))
  obtain ⟨W,hW,hclose⟩ := (isCompact_sphere c R).mem_uniformity_of_prod hF.continuousOn
    (mem_univ q) (Metric.dist_mem_uniformity hδ)
  rw [nhdsWithin_univ] at hW
  have hevent : ∀ᶠ a in 𝓝 q, analyticZeroCount (hillHminusRadicand a) (closedBall c R) = 2 ∧
      ∀ z ∈ sphere c R, hillHminusRadicand a z ≠ 0 := by
    filter_upwards [hcount,hW] with a ha hWa
    refine ⟨ha.trans (hillHminusRealGapContour_count_two q hr n hn),?_⟩
    intro z hz hzero
    have hh := hclose a hWa z hz
    change dist (F a z) (F q z) < δ at hh
    change F a z = 0 at hzero
    rw [hzero,dist_zero_left] at hh
    exact (not_lt_of_ge (hbound z hz)) hh
  obtain ⟨V,hVsub,hV,hqV⟩ := _root_.mem_nhds_iff.mp hevent
  exact ⟨V,hV,hqV,fun a ha => hVsub ha⟩

end NLS.KdV
