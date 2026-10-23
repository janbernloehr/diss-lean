import NLS.FunctionalAnalysis.RealSheetEndpoint

/-! # Recurrence of endpoint visits on a bounded real spectral sheet

A complete bounded sheet trajectory has zeros of velocity arbitrarily
late in time. The proof only assumes a fixed velocity sign on a tail:
clamping that tail gives a monotone bounded function with the same limit.
-/
noncomputable section
open Set Filter Topology
namespace NLS.FunctionalAnalysis

/-- A complete bounded real sheet trajectory reaches a zero of velocity
after every prescribed time when every sheet zero has nonzero acceleration. -/
theorem exists_future_zero_velocity_of_bounded_sheetODE
    (x v F G : ℝ → ℝ) (a b : ℝ)
    (hxder : ∀ t, HasDerivAt x (v t) t)
    (hvder : ∀ t, HasDerivAt v (F (x t)) t)
    (hx : ∀ t, x t ∈ Icc a b) (hsheet : ∀ t, (v t)^2 = G (x t))
    (hF : Continuous F) (hG : Continuous G)
    (hzeros : ∀ y ∈ Icc a b, G y = 0 → F y ≠ 0) :
    ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧ v t = 0 := by
  intro T
  by_contra hnever
  push Not at hnever
  have hvC : Continuous v := continuous_iff_continuousAt.mpr (fun t => (hvder t).continuousAt)
  have hsign : (∀ t, T ≤ t → 0 < v t) ∨ (∀ t, T ≤ t → v t < 0) := by
    by_cases hpos : 0 < v T
    · left
      intro t ht
      by_contra hn
      obtain ⟨u,hu,he⟩ := intermediate_value_Icc' ht hvC.continuousOn ⟨not_lt.mp hn,hpos.le⟩
      exact hnever u hu.1 he
    · right
      have hneg : v T < 0 := lt_of_le_of_ne (not_lt.mp hpos) (hnever T le_rfl)
      intro t ht
      by_contra hn
      obtain ⟨u,hu,he⟩ := intermediate_value_Icc ht hvC.continuousOn ⟨hneg.le,not_lt.mp hn⟩
      exact hnever u hu.1 he
  have hxB : ∀ t, ‖x t‖ ≤ |a|+|b| := by
    intro t
    rw [Real.norm_eq_abs,abs_le]
    constructor
    · have ha := neg_abs_le a
      have hb := abs_nonneg b
      linarith [(hx t).1]
    · linarith [(hx t).2,le_abs_self b,abs_nonneg a]
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hG.continuousOn
  have hvB : ∀ t, ‖v t‖ ≤ max B 0+1 := by
    intro t
    have hs : (v t)^2 ≤ B := by
      rw [hsheet t]
      exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB (x t) (hx t))
    rw [Real.norm_eq_abs]
    nlinarith [sq_abs (v t),abs_nonneg (v t),le_max_left B 0,le_max_right B 0]
  have hxC : Continuous x := continuous_iff_continuousAt.mpr (fun t => (hxder t).continuousAt)
  have hclamp : (fun t => x (max T t)) =ᶠ[atTop] x := by
    filter_upwards [eventually_ge_atTop T] with t ht
    rw [max_eq_right ht]
  have hxlim : ∃ l : ℝ, Tendsto x atTop (𝓝 l) := by
    rcases hsign with hpos | hneg
    · have hm : MonotoneOn x (Ici T) := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici T)
        hxC.continuousOn (fun t _ => (hxder t).hasDerivWithinAt)
        (fun t ht => (hpos t (interior_subset ht)).le)
      have hc : Monotone (fun t => x (max T t)) := fun s t hst =>
        hm (show max T s ∈ Ici T from le_max_left T s)
          (show max T t ∈ Ici T from le_max_left T t) (max_le_max_left T hst)
      exact ⟨iSup (fun t => x (max T t)),(tendsto_atTop_ciSup hc
        ⟨b,by rintro _ ⟨t,rfl⟩; exact (hx (max T t)).2⟩).congr' hclamp⟩
    · have hm : AntitoneOn x (Ici T) := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici T)
        hxC.continuousOn (fun t _ => (hxder t).hasDerivWithinAt)
        (fun t ht => (hneg t (interior_subset ht)).le)
      have hc : Antitone (fun t => x (max T t)) := fun s t hst =>
        hm (show max T s ∈ Ici T from le_max_left T s)
          (show max T t ∈ Ici T from le_max_left T t) (max_le_max_left T hst)
      exact ⟨iInf (fun t => x (max T t)),(tendsto_atTop_ciInf hc
        ⟨a,by rintro _ ⟨t,rfl⟩; exact (hx (max T t)).1⟩).congr' hclamp⟩
  obtain ⟨l,hl⟩ := hxlim
  have hlmem : l ∈ Icc a b :=
    ⟨le_of_tendsto_of_tendsto' tendsto_const_nhds hl (fun t => (hx t).1),
      le_of_tendsto_of_tendsto' hl tendsto_const_nhds (fun t => (hx t).2)⟩
  have hGlim : Tendsto (fun t => G (x t)) atTop (𝓝 (G l)) := hG.continuousAt.tendsto.comp hl
  have hvlim : ∃ q : ℝ, Tendsto v atTop (𝓝 q) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hGlim
    rcases hsign with hpos | hneg
    · refine ⟨Real.sqrt (G l),hsqrt.congr' ?_⟩
      filter_upwards [eventually_ge_atTop T] with t ht
      change Real.sqrt (G (x t)) = v t
      rw [← hsheet t,Real.sqrt_sq (hpos t ht).le]
    · refine ⟨-Real.sqrt (G l),hsqrt.neg.congr' ?_⟩
      filter_upwards [eventually_ge_atTop T] with t ht
      change -Real.sqrt (G (x t)) = v t
      rw [← hsheet t,Real.sqrt_sq_eq_abs,abs_of_neg (hneg t ht),neg_neg]
  obtain ⟨q,hq⟩ := hvlim
  have hq0 : q = 0 := derivative_limit_eq_zero_of_bounded x v hxder (|a|+|b|) hxB q hq
  have hv0 : Tendsto v atTop (𝓝 (0 : ℝ)) := by simpa only [hq0] using hq
  have hG0 : G l = 0 := by
    have hs := (hv0.pow 2).congr' (Filter.Eventually.of_forall hsheet)
    exact (tendsto_nhds_unique hGlim hs).trans (by norm_num)
  have hF0 : F l = 0 := derivative_limit_eq_zero_of_bounded v (fun t => F (x t)) hvder
    (max B 0+1) hvB (F l) (hF.continuousAt.tendsto.comp hl)
  exact hzeros l hlmem hG0 hF0

end NLS.FunctionalAnalysis
