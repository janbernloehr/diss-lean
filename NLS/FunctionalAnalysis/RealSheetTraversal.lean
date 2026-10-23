import NLS.FunctionalAnalysis.RealSheetRecurrence
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # Complete traversal of a bounded real spectral sheet

Successive turning points bound directed segments of a complete trajectory.
Nonzero acceleration at every sheet zero forces both velocity signs to occur;
the trajectory therefore covers every admissible point on both branches.
-/
noncomputable section
open Set Filter Topology
namespace NLS.FunctionalAnalysis

private theorem exists_first_zero_after_positive
    (v : ℝ → ℝ) (hv : Continuous v) (T : ℝ) (hT : 0 < v T)
    (hex : ∃ t : ℝ, T ≤ t ∧ v t = 0) :
    ∃ t : ℝ, T < t ∧ v t = 0 ∧ ∀ s ∈ Ico T t, 0 < v s := by
  obtain ⟨b,hTb,hb⟩ := hex
  let Z := Icc T b ∩ v ⁻¹' {0}
  have hc : IsCompact Z := isCompact_Icc.inter_right (isClosed_singleton.preimage hv)
  obtain ⟨t,ht,hmin⟩ := hc.exists_isLeast ⟨b,⟨⟨hTb,le_rfl⟩,hb⟩⟩
  have ht0 : v t = 0 := ht.2
  have hTt : T < t := lt_of_le_of_ne ht.1.1 (by
    intro he
    have hz : v T = 0 := he ▸ ht0
    linarith)
  refine ⟨t,hTt,ht0,?_⟩
  intro s hs
  by_contra hpos
  obtain ⟨u,hu,he⟩ := intermediate_value_Icc' hs.1 hv.continuousOn ⟨not_lt.mp hpos,hT.le⟩
  have hut : t ≤ u := hmin ⟨⟨hu.1,hu.2.trans (hs.2.le.trans ht.1.2)⟩,he⟩
  exact (not_le_of_gt hs.2) (hut.trans hu.2)

/-- The next velocity zero after a positive-velocity point is the upper endpoint,
and the velocity remains positive up to that time. -/
theorem exists_upper_turning_time_of_positive_sheetODE
    (x v F G : ℝ → ℝ) (a b : ℝ)
    (hxder : ∀ t, HasDerivAt x (v t) t)
    (hvder : ∀ t, HasDerivAt v (F (x t)) t)
    (hx : ∀ t, x t ∈ Icc a b) (hsheet : ∀ t, (v t)^2 = G (x t))
    (hF : Continuous F) (hG : Continuous G)
    (hzeros : ∀ y ∈ Icc a b, G y = 0 → F y ≠ 0)
    (hends : ∀ y ∈ Icc a b, G y = 0 → y = a ∨ y = b)
    (ha : G a = 0) (T : ℝ) (hT : 0 < v T) :
    ∃ t : ℝ, T < t ∧ x t = b ∧ v t = 0 ∧ ∀ s ∈ Ico T t, 0 < v s := by
  have hvC : Continuous v := continuous_iff_continuousAt.mpr (fun t => (hvder t).continuousAt)
  obtain ⟨t,ht,hvt,hpos⟩ := exists_first_zero_after_positive v hvC T hT
    (exists_future_zero_velocity_of_bounded_sheetODE x v F G a b hxder hvder hx hsheet hF hG hzeros T)
  have hxa : a < x T := by
    apply lt_of_le_of_ne (hx T).1
    intro he
    have hs := hsheet T
    rw [← he,ha] at hs
    nlinarith
  have hm : MonotoneOn x (Icc T t) := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc T t)
    ((continuous_iff_continuousAt.mpr (fun t => (hxder t).continuousAt)).continuousOn)
    (fun u _ => (hxder u).hasDerivWithinAt) (fun u hu => by
      simp only [interior_Icc,mem_Ioo] at hu
      exact (hpos u ⟨hu.1.le,hu.2⟩).le)
  have hxt : x T ≤ x t := hm ⟨le_rfl,ht.le⟩ ⟨ht.le,le_rfl⟩ ht.le
  have hend := hends (x t) (hx t) (by rw [← hsheet t,hvt]; norm_num)
  have hxb : x t = b := hend.resolve_left (fun he => (not_le_of_gt hxa) (he ▸ hxt))
  exact ⟨t,ht,hxb,hvt,hpos⟩

/-- Every admissible point above a positive-velocity initial position is reached
with the prescribed nonnegative velocity, including the upper turning point. -/
theorem exists_forward_upper_sheet_point
    (x v F G : ℝ → ℝ) (a b : ℝ)
    (hxder : ∀ t, HasDerivAt x (v t) t)
    (hvder : ∀ t, HasDerivAt v (F (x t)) t)
    (hx : ∀ t, x t ∈ Icc a b) (hsheet : ∀ t, (v t)^2 = G (x t))
    (hF : Continuous F) (hG : Continuous G)
    (hzeros : ∀ y ∈ Icc a b, G y = 0 → F y ≠ 0)
    (hends : ∀ y ∈ Icc a b, G y = 0 → y = a ∨ y = b)
    (ha : G a = 0) (T : ℝ) (hT : 0 < v T)
    (y w : ℝ) (hy : y ∈ Icc (x T) b) (hw : 0 ≤ w) (hs : w^2 = G y) :
    ∃ u : ℝ, T ≤ u ∧ x u = y ∧ v u = w := by
  obtain ⟨t,ht,hxt,hvt,hpos⟩ := exists_upper_turning_time_of_positive_sheetODE x v F G a b
    hxder hvder hx hsheet hF hG hzeros hends ha T hT
  have hxC : Continuous x := continuous_iff_continuousAt.mpr (fun t => (hxder t).continuousAt)
  obtain ⟨u,hu,huy⟩ := intermediate_value_Icc ht.le hxC.continuousOn (by simpa only [hxt] using hy)
  have hvu : 0 ≤ v u := by
    rcases hu.2.eq_or_lt with he | he
    · rw [he,hvt]
    · exact (hpos u ⟨hu.1,he⟩).le
  refine ⟨u,hu.1,huy,?_⟩
  apply (sq_eq_sq₀ hvu hw).mp
  rw [hsheet u,huy,hs]

/-- The next zero after a negative-velocity point is the lower endpoint. -/
theorem exists_lower_turning_time_of_negative_sheetODE
    (x v F G : ℝ → ℝ) (a b : ℝ)
    (hxder : ∀ t, HasDerivAt x (v t) t)
    (hvder : ∀ t, HasDerivAt v (F (x t)) t)
    (hx : ∀ t, x t ∈ Icc a b) (hsheet : ∀ t, (v t)^2 = G (x t))
    (hF : Continuous F) (hG : Continuous G)
    (hzeros : ∀ y ∈ Icc a b, G y = 0 → F y ≠ 0)
    (hends : ∀ y ∈ Icc a b, G y = 0 → y = a ∨ y = b)
    (hb : G b = 0) (T : ℝ) (hT : v T < 0) :
    ∃ t : ℝ, T < t ∧ x t = a ∧ v t = 0 ∧ ∀ s ∈ Ico T t, v s < 0 := by
  have hvC : Continuous v := continuous_iff_continuousAt.mpr (fun t => (hvder t).continuousAt)
  have hex : ∃ t : ℝ, T ≤ t ∧ -v t = 0 := by
    simpa only [neg_eq_zero] using
      exists_future_zero_velocity_of_bounded_sheetODE x v F G a b hxder hvder hx hsheet hF hG hzeros T
  obtain ⟨t,ht,hvt,hneg⟩ := exists_first_zero_after_positive (fun t => -v t) hvC.neg T (neg_pos.mpr hT) hex
  simp only [neg_eq_zero,neg_pos] at hvt hneg
  have hxb : x T < b := by
    apply lt_of_le_of_ne (hx T).2
    intro he
    have hs := hsheet T
    rw [he,hb] at hs
    nlinarith
  have hm : AntitoneOn x (Icc T t) := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc T t)
    ((continuous_iff_continuousAt.mpr (fun t => (hxder t).continuousAt)).continuousOn)
    (fun u _ => (hxder u).hasDerivWithinAt) (fun u hu => by
      simp only [interior_Icc,mem_Ioo] at hu
      exact (hneg u ⟨hu.1.le,hu.2⟩).le)
  have hxt : x t ≤ x T := hm ⟨le_rfl,ht.le⟩ ⟨ht.le,le_rfl⟩ ht.le
  have hend := hends (x t) (hx t) (by rw [← hsheet t,hvt]; norm_num)
  have hxa : x t = a := hend.resolve_right (fun he => (not_le_of_gt hxb) (he ▸ hxt))
  exact ⟨t,ht,hxa,hvt,hneg⟩

/-- Every admissible point below a negative-velocity initial position is reached
with its prescribed nonpositive velocity before the lower turning point. -/
theorem exists_forward_lower_sheet_point
    (x v F G : ℝ → ℝ) (a b : ℝ)
    (hxder : ∀ t, HasDerivAt x (v t) t)
    (hvder : ∀ t, HasDerivAt v (F (x t)) t)
    (hx : ∀ t, x t ∈ Icc a b) (hsheet : ∀ t, (v t)^2 = G (x t))
    (hF : Continuous F) (hG : Continuous G)
    (hzeros : ∀ y ∈ Icc a b, G y = 0 → F y ≠ 0)
    (hends : ∀ y ∈ Icc a b, G y = 0 → y = a ∨ y = b)
    (hb : G b = 0) (T : ℝ) (hT : v T < 0)
    (y w : ℝ) (hy : y ∈ Icc a (x T)) (hw : w ≤ 0) (hs : w^2 = G y) :
    ∃ u : ℝ, T ≤ u ∧ x u = y ∧ v u = w := by
  obtain ⟨t,ht,hxt,hvt,hneg⟩ := exists_lower_turning_time_of_negative_sheetODE x v F G a b
    hxder hvder hx hsheet hF hG hzeros hends hb T hT
  have hxC : Continuous x := continuous_iff_continuousAt.mpr (fun t => (hxder t).continuousAt)
  obtain ⟨u,hu,huy⟩ := intermediate_value_Icc' ht.le hxC.continuousOn (by simpa only [hxt] using hy)
  have hvu : v u ≤ 0 := by
    rcases hu.2.eq_or_lt with he | he
    · rw [he,hvt]
    · exact (hneg u ⟨hu.1,he⟩).le
  refine ⟨u,hu.1,huy,?_⟩
  apply neg_injective
  apply (sq_eq_sq₀ (neg_nonneg.mpr hvu) (neg_nonneg.mpr hw)).mp
  rw [neg_sq,neg_sq,hsheet u,huy,hs]

/-- From any positive-velocity point, the complete trajectory covers the entire
nonnegative branch, using forward time above it and reversed time below it. -/
theorem exists_nonnegative_sheet_point_of_positive_velocity
    (x v F G : ℝ → ℝ) (a b : ℝ)
    (hxder : ∀ t, HasDerivAt x (v t) t)
    (hvder : ∀ t, HasDerivAt v (F (x t)) t)
    (hx : ∀ t, x t ∈ Icc a b) (hsheet : ∀ t, (v t)^2 = G (x t))
    (hF : Continuous F) (hG : Continuous G)
    (hzeros : ∀ y ∈ Icc a b, G y = 0 → F y ≠ 0)
    (hends : ∀ y ∈ Icc a b, G y = 0 → y = a ∨ y = b)
    (ha : G a = 0) (hb : G b = 0) (T : ℝ) (hT : 0 < v T)
    (y w : ℝ) (hy : y ∈ Icc a b) (hw : 0 ≤ w) (hs : w^2 = G y) :
    ∃ u : ℝ, x u = y ∧ v u = w := by
  rcases le_total (x T) y with hup | hdown
  · obtain ⟨u,_,hu,hv⟩ := exists_forward_upper_sheet_point x v F G a b
      hxder hvder hx hsheet hF hG hzeros hends ha T hT y w ⟨hup,hy.2⟩ hw hs
    exact ⟨u,hu,hv⟩
  · have hxrev (t : ℝ) : HasDerivAt (fun u => x (-u)) (-v (-t)) t := by
      simpa only [Function.comp_def,mul_neg_one] using (hxder (-t)).comp t (hasDerivAt_neg t)
    have hvrev (t : ℝ) : HasDerivAt (fun u => -v (-u)) (F (x (-t))) t := by
      convert ((hvder (-t)).comp t (hasDerivAt_neg t)).neg using 1 <;>
        first | rfl | simp
    obtain ⟨u,_,hu,hv⟩ := exists_forward_lower_sheet_point
      (fun t => x (-t)) (fun t => -v (-t)) F G a b hxrev hvrev (fun t => hx (-t))
      (fun t => by simpa only [neg_sq] using hsheet (-t)) hF hG hzeros hends hb (-T)
      (by simpa only [neg_neg,neg_lt_zero] using hT) y (-w)
      (by simpa only [neg_neg,mem_Icc] using And.intro hy.1 hdown) (neg_nonpos.mpr hw)
      (by simpa only [neg_sq] using hs)
    exact ⟨-u,hu,neg_injective hv⟩

/-- Nonzero acceleration at a turning point forces both velocity signs to occur. -/
theorem exists_both_velocity_signs_of_bounded_sheetODE
    (x v F G : ℝ → ℝ) (a b : ℝ)
    (hxder : ∀ t, HasDerivAt x (v t) t)
    (hvder : ∀ t, HasDerivAt v (F (x t)) t)
    (hx : ∀ t, x t ∈ Icc a b) (hsheet : ∀ t, (v t)^2 = G (x t))
    (hF : Continuous F) (hG : Continuous G)
    (hzeros : ∀ y ∈ Icc a b, G y = 0 → F y ≠ 0) :
    (∃ t, 0 < v t) ∧ (∃ t, v t < 0) := by
  obtain ⟨t,_,ht⟩ := exists_future_zero_velocity_of_bounded_sheetODE x v F G a b
    hxder hvder hx hsheet hF hG hzeros 0
  have hne := hzeros (x t) (hx t) (by rw [← hsheet t,ht]; norm_num)
  constructor
  · by_contra hn
    push Not at hn
    have hm : IsLocalMax v t := Filter.Eventually.of_forall (fun u => by rw [ht]; exact hn u)
    exact hne (hm.hasDerivAt_eq_zero (hvder t))
  · by_contra hn
    push Not at hn
    have hm : IsLocalMin v t := Filter.Eventually.of_forall (fun u => by rw [ht]; exact hn u)
    exact hne (hm.hasDerivAt_eq_zero (hvder t))

/-- A complete bounded trajectory covers every point of the two-sided real sheet,
including both turning points, when those are its only sheet zeros. -/
theorem exists_point_of_complete_bounded_sheetODE
    (x v F G : ℝ → ℝ) (a b : ℝ)
    (hxder : ∀ t, HasDerivAt x (v t) t)
    (hvder : ∀ t, HasDerivAt v (F (x t)) t)
    (hx : ∀ t, x t ∈ Icc a b) (hsheet : ∀ t, (v t)^2 = G (x t))
    (hF : Continuous F) (hG : Continuous G)
    (hzeros : ∀ y ∈ Icc a b, G y = 0 → F y ≠ 0)
    (hends : ∀ y ∈ Icc a b, G y = 0 → y = a ∨ y = b)
    (ha : G a = 0) (hb : G b = 0)
    (y w : ℝ) (hy : y ∈ Icc a b) (hs : w^2 = G y) :
    ∃ u : ℝ, x u = y ∧ v u = w := by
  obtain ⟨⟨T,hT⟩,⟨S,hS⟩⟩ := exists_both_velocity_signs_of_bounded_sheetODE x v F G a b
    hxder hvder hx hsheet hF hG hzeros
  rcases le_total 0 w with hw | hw
  · exact exists_nonnegative_sheet_point_of_positive_velocity x v F G a b
      hxder hvder hx hsheet hF hG hzeros hends ha hb T hT y w hy hw hs
  · have hxrev (t : ℝ) : HasDerivAt (fun u => x (-u)) (-v (-t)) t := by
      simpa only [Function.comp_def,mul_neg_one] using (hxder (-t)).comp t (hasDerivAt_neg t)
    have hvrev (t : ℝ) : HasDerivAt (fun u => -v (-u)) (F (x (-t))) t := by
      convert ((hvder (-t)).comp t (hasDerivAt_neg t)).neg using 1 <;>
        first | rfl | simp
    obtain ⟨u,hu,hv⟩ := exists_nonnegative_sheet_point_of_positive_velocity
      (fun t => x (-t)) (fun t => -v (-t)) F G a b hxrev hvrev (fun t => hx (-t))
      (fun t => by simpa only [neg_sq] using hsheet (-t)) hF hG hzeros hends ha hb (-S)
      (by simpa only [neg_neg,neg_pos] using hS) y (-w) hy (neg_nonneg.mpr hw)
      (by simpa only [neg_sq] using hs)
    exact ⟨-u,hu,neg_injective hv⟩

end NLS.FunctionalAnalysis
