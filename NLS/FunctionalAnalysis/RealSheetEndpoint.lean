import NLS.FunctionalAnalysis.BoundedDerivativeLimit
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Endpoint reachability on a bounded real spectral sheet

If the velocity never vanishes, continuity fixes its sign and the bounded
position is monotone. The position and velocity then have finite limits.
Boundedness forces the limiting velocity and acceleration to be zero,
contradicting nonzero acceleration at a zero of the sheet equation.
-/

noncomputable section
open Set Filter Topology
namespace NLS.FunctionalAnalysis

/-- A complete bounded real sheet trajectory reaches a zero of its
velocity if the sheet zeros have nonzero acceleration. The trajectory
and sheet equation are actual equations, with no reachability premise. -/
theorem exists_zero_velocity_of_bounded_sheetODE
    (x v F G : ℝ → ℝ) (a b : ℝ)
    (hxder : ∀ t, HasDerivAt x (v t) t)
    (hvder : ∀ t, HasDerivAt v (F (x t)) t)
    (hx : ∀ t, x t ∈ Icc a b) (hsheet : ∀ t, (v t)^2 = G (x t))
    (hF : Continuous F) (hG : Continuous G)
    (hzeros : ∀ y ∈ Icc a b, G y = 0 → F y ≠ 0) :
    ∃ t : ℝ, v t = 0 := by
  by_contra hnever
  push Not at hnever
  have hvC : Continuous v := continuous_iff_continuousAt.mpr (fun t => (hvder t).continuousAt)
  have hsign : (∀ t, 0 < v t) ∨ (∀ t, v t < 0) := by
    by_cases hpos : 0 < v 0
    · left
      intro t
      by_contra ht
      obtain ⟨u,hu⟩ := intermediate_value_univ t 0 hvC ⟨not_lt.mp ht,hpos.le⟩
      exact hnever u hu
    · right
      have hneg : v 0 < 0 := lt_of_le_of_ne (not_lt.mp hpos) (hnever 0)
      intro t
      by_contra ht
      obtain ⟨u,hu⟩ := intermediate_value_univ 0 t hvC ⟨hneg.le,not_lt.mp ht⟩
      exact hnever u hu
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
  have hxlim : ∃ l : ℝ, Tendsto x atTop (𝓝 l) := by
    rcases hsign with hpos | hneg
    · have hm : Monotone x := monotone_of_hasDerivAt_nonneg hxder (fun t => (hpos t).le)
      exact ⟨iSup x,tendsto_atTop_ciSup hm ⟨b,by rintro _ ⟨t,rfl⟩; exact (hx t).2⟩⟩
    · have hm : Antitone x := antitone_of_deriv_nonpos
        (fun t => (hxder t).differentiableAt) (fun t => by rw [(hxder t).deriv]; exact (hneg t).le)
      exact ⟨iInf x,tendsto_atTop_ciInf hm ⟨a,by rintro _ ⟨t,rfl⟩; exact (hx t).1⟩⟩
  obtain ⟨l,hl⟩ := hxlim
  have hlmem : l ∈ Icc a b :=
    ⟨le_of_tendsto_of_tendsto' tendsto_const_nhds hl (fun t => (hx t).1),
      le_of_tendsto_of_tendsto' hl tendsto_const_nhds (fun t => (hx t).2)⟩
  have hGlim : Tendsto (fun t => G (x t)) atTop (𝓝 (G l)) := hG.continuousAt.tendsto.comp hl
  have hvlim : ∃ q : ℝ, Tendsto v atTop (𝓝 q) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hGlim
    rcases hsign with hpos | hneg
    · have he : v = fun t => Real.sqrt (G (x t)) := by
        funext t
        rw [← hsheet t,Real.sqrt_sq (hpos t).le]
      exact ⟨Real.sqrt (G l),by rw [he]; exact hsqrt⟩
    · have he : v = fun t => -Real.sqrt (G (x t)) := by
        funext t
        rw [← hsheet t,Real.sqrt_sq_eq_abs,abs_of_neg (hneg t),neg_neg]
      exact ⟨-Real.sqrt (G l),by rw [he]; exact hsqrt.neg⟩
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
