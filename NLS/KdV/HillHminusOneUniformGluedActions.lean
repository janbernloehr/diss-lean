import NLS.KdV.HillHminusOneGluedHighActions

/-! # Uniform normalization of the chart-independent native high actions

One open complex neighborhood lies in every later high action domain.
The glued ratio has the original locally uniform normalization, and the
glued action vanishes exactly with its actual gap square there.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
namespace NLS.KdV

theorem hillHminusGluedHighAction_eq_zero_iff
    (n : ℕ+) (q : PeriodOneHminusOne) (hR : hillHminusGluedHighActionRatio n q ≠ 0) :
    hillHminusGluedHighAction n q = 0 ↔ hillHminusGluedHighGapSquare n q = 0 := by
  have hc : (8*((Real.pi : ℂ)*(n : ℕ))) ≠ 0 := by simp [Real.pi_ne_zero,n.ne_zero]
  rw [hillHminusGluedHighAction,mul_eq_zero,div_eq_zero_iff]
  simp only [hR,hc,or_false]

theorem hillHminusGluedHighAction_normalized_quotient
    (n : ℕ+) (q : PeriodOneHminusOne) (hg : hillHminusGluedHighGapSquare n q ≠ 0) :
    (8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusGluedHighAction n q/hillHminusGluedHighGapSquare n q =
      hillHminusGluedHighActionRatio n q := by
  have hc : (8*((Real.pi : ℂ)*(n : ℕ))) ≠ 0 := by simp [Real.pi_ne_zero,n.ne_zero]
  rw [hillHminusGluedHighAction]
  field_simp [hg,hc]

theorem norm_hillHminusGluedHighAction_error_le
    (n : ℕ+) (q : PeriodOneHminusOne) (epsilon : ℝ)
    (hR : ‖hillHminusGluedHighActionRatio n q-1‖ ≤ epsilon) :
    ‖(8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusGluedHighAction n q-hillHminusGluedHighGapSquare n q‖ ≤
      ‖hillHminusGluedHighGapSquare n q‖*epsilon := by
  have hc : (8*((Real.pi : ℂ)*(n : ℕ))) ≠ 0 := by simp [Real.pi_ne_zero,n.ne_zero]
  have he : (8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusGluedHighAction n q-hillHminusGluedHighGapSquare n q =
      hillHminusGluedHighGapSquare n q*(hillHminusGluedHighActionRatio n q-1) := by
    rw [hillHminusGluedHighAction]
    field_simp [hc]
  rw [he,norm_mul]
  exact mul_le_mul_of_nonneg_left hR (norm_nonneg _)

theorem exists_hillHminus_uniform_glued_high_actions (q : PeriodOneHminusOne)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, 0 < N ∧ IsOpen V ∧ q ∈ V ∧
      ∀ n : ℕ+, N ≤ (n : ℕ) → V ⊆ hillHminusHighActionDomain n ∧
        ∀ a ∈ V, ‖hillHminusGluedHighActionRatio n a-1‖ ≤ epsilon ∧
          hillHminusGluedHighActionRatio n a ≠ 0 ∧
          (hillHminusGluedHighAction n a = 0 ↔ hillHminusGluedHighGapSquare n a = 0) ∧
          ‖(8*((Real.pi : ℂ)*(n : ℕ)))*hillHminusGluedHighAction n a-hillHminusGluedHighGapSquare n a‖ ≤
            ‖hillHminusGluedHighGapSquare n a‖*epsilon := by
  obtain ⟨r,_,_,hfamily⟩ := exists_hillHminus_uniform_action_neighborhoods q
  obtain ⟨N,V,hN,hV,hq,hfamily⟩ := hfamily epsilon hepsilon
  refine ⟨N,V,hN,hV,hq,?_⟩
  intro n hn
  obtain ⟨K,hK,hR⟩ := hfamily n hn
  refine ⟨fun a ha => hK.mem_highActionDomain ha,?_⟩
  intro a ha
  have he := hK.glued_ratio_eq ha
  have hb : ‖hillHminusGluedHighActionRatio n a-1‖ ≤ epsilon := by rw [he]; exact (hR a ha).1
  have hz : hillHminusGluedHighActionRatio n a ≠ 0 := by rw [he]; exact (hR a ha).2
  exact ⟨hb,hz,hillHminusGluedHighAction_eq_zero_iff n a hz,norm_hillHminusGluedHighAction_error_le n a epsilon hb⟩

end NLS.KdV
