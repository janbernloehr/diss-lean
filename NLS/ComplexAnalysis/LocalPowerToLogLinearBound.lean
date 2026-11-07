import NLS.ComplexAnalysis.BanachAnalyticZeroBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Local power decay and the source norm factor

For an analytic family vanishing at zero, locally uniform power bounds
imply power bounds linear in the source norm. An unbounded logarithmic
factor then absorbs the local constants after a locally uniform cutoff.
-/
noncomputable section
open Set Metric Filter Topology
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem exists_local_linear_power_bound
    (f : ℕ+ → E → F) (a : ℕ+ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hzero : ∀ n, f n 0 = 0)
    (hlocal : ∀ x : E, ∃ N : ℕ, ∃ U : Set E, ∃ B : ℝ,
      IsOpen U ∧ x ∈ U ∧ 0 ≤ B ∧ ∀ n : ℕ+, N ≤ (n:ℕ) →
        AnalyticOnNhd ℂ (f n) U ∧ ∀ y ∈ U, ‖f n y‖ ≤ B*a n)
    (x : E) :
    ∃ N : ℕ, ∃ U : Set E, ∃ B : ℝ,
      IsOpen U ∧ x ∈ U ∧ 0 ≤ B ∧
        ∀ n : ℕ+, N ≤ (n:ℕ) → ∀ y ∈ U, ‖f n y‖ ≤ B*a n*‖y‖ := by
  by_cases hx : x = 0
  · subst x
    obtain ⟨N,U,B,hU,h0,hB,hbound⟩ := hlocal 0
    obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
    refine ⟨N,ball 0 (δ/4),8*B/δ,isOpen_ball,mem_ball_self (by positivity),by positivity,?_⟩
    intro n hn y hy
    have hf := (hbound n hn).1.mono hsub
    have hb := fun z hz => (hbound n hn).2 z (hsub hz)
    exact (norm_le_mul_norm_of_analytic_zero_ball_bound
      (f n) δ (B*a n) hδ hf (hzero n) hb y hy).trans_eq (by ring)
  · obtain ⟨N,U,B,hU,hxU,hB,hbound⟩ := hlocal x
    have hxp : 0 < ‖x‖ := norm_pos_iff.mpr hx
    let V := U ∩ {y : E | ‖x‖/2 < ‖y‖}
    have hV : IsOpen V := hU.inter (isOpen_lt continuous_const continuous_norm)
    refine ⟨N,V,B/(‖x‖/2),hV,⟨hxU,by change ‖x‖/2 < ‖x‖; linarith⟩,by positivity,?_⟩
    intro n hn y hy
    have hfactor : B ≤ (B/(‖x‖/2))*‖y‖ := by
      have hh := mul_le_mul_of_nonneg_left hy.2.le
        (show 0 ≤ B/(‖x‖/2) by positivity)
      rw [div_mul_cancel₀ B (ne_of_gt (half_pos hxp))] at hh
      exact hh
    exact ((hbound n hn).2 y hy.1).trans
      ((mul_le_mul_of_nonneg_right hfactor (ha n)).trans_eq (by ring))

theorem exists_local_log_squared_linear_power_bound
    (f : ℕ+ → E → F) (a : ℕ+ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hzero : ∀ n, f n 0 = 0)
    (hlocal : ∀ x : E, ∃ N : ℕ, ∃ U : Set E, ∃ B : ℝ,
      IsOpen U ∧ x ∈ U ∧ 0 ≤ B ∧ ∀ n : ℕ+, N ≤ (n:ℕ) →
        AnalyticOnNhd ℂ (f n) U ∧ ∀ y ∈ U, ‖f n y‖ ≤ B*a n)
    (x : E) (Nmin : ℕ) :
    ∃ N : ℕ, ∃ U : Set E,
      Nmin ≤ N ∧ IsOpen U ∧ x ∈ U ∧
        ∀ n : ℕ+, N ≤ (n:ℕ) → ∀ y ∈ U, ‖f n y‖ ≤ (Real.log (n:ℝ))^2*a n*‖y‖ := by
  obtain ⟨N,U,B,hU,hx,hB,hbound⟩ := exists_local_linear_power_bound f a ha hzero hlocal x
  have hl : Tendsto (fun n : ℕ => Real.log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (hl.eventually_ge_atTop (max B 1))
  refine ⟨max N (max J Nmin),U,le_trans (le_max_right _ _) (le_max_right _ _),hU,hx,?_⟩
  intro n hn y hy
  have hnN : N ≤ (n:ℕ) := (le_max_left _ _).trans hn
  have hnJ : J ≤ (n:ℕ) := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hn
  have hb : B ≤ Real.log (n:ℝ) := (le_max_left _ _).trans (hJ (n:ℕ) hnJ)
  have h1 : 1 ≤ Real.log (n:ℝ) := (le_max_right _ _).trans (hJ (n:ℕ) hnJ)
  have hsq : B ≤ (Real.log (n:ℝ))^2 := by nlinarith
  exact (hbound n hnN y hy).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq (ha n)) (norm_nonneg y))

end NLS.ComplexAnalysis
