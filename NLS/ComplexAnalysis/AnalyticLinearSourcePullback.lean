import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear

/-! # Common source balls and native analytic bounded-linear pullbacks -/
noncomputable section
open Set Metric
namespace NLS.ComplexAnalysis
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- One source ball lies in two prescribed target neighborhoods and a
prescribed source norm bound under a bounded linear map. -/
theorem exists_common_ball_linear_preimage (L : E →L[ℂ] F) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (V : Set F) (hV : IsOpen V) (h0V : (0 : F) ∈ V) :
    ∃ η : ℝ, 0 < η ∧ ∀ u ∈ ball (0 : E) η, L u ∈ ball (0 : F) δ ∧ L u ∈ V ∧ ‖u‖ ≤ ε := by
  let U : Set E := (L ⁻¹' (ball (0 : F) δ ∩ V)) ∩ ball 0 ε
  have hU : IsOpen U := ((isOpen_ball.inter hV).preimage L.continuous).inter isOpen_ball
  have h0U : (0 : E) ∈ U := by
    change (L 0 ∈ ball (0 : F) δ ∩ V) ∧ (0 : E) ∈ ball 0 ε
    rw [map_zero]
    exact ⟨⟨mem_ball_self hδ,h0V⟩,mem_ball_self hε⟩
  obtain ⟨η,hη,hηU⟩ := Metric.isOpen_iff.mp hU 0 h0U
  refine ⟨η,hη,?_⟩
  intro u hu
  have hs := hηU hu
  exact ⟨hs.1.1,hs.1.2,(mem_ball_zero_iff.mp hs.2).le⟩

/-- A joint native analytic family pulls back along a bounded linear
source map on a common source ball. -/
theorem analyticOnNhd_product_linear_pullback (L : E →L[ℂ] F) (δ η : ℝ)
    (P : ℂ × F → G) (hP : AnalyticOnNhd ℂ P (univ ×ˢ ball (0 : F) δ))
    (hsource : ∀ u ∈ ball (0 : E) η, L u ∈ ball (0 : F) δ) :
    AnalyticOnNhd ℂ (fun t : ℂ × E => P (t.1,L t.2)) (univ ×ˢ ball (0 : E) η) := by
  intro t ht
  have hJ : AnalyticAt ℂ (fun x : ℂ × E => (x.1,L x.2)) t :=
    analyticAt_fst.prod ((L.analyticAt _).comp analyticAt_snd)
  exact (hP (t.1,L t.2) ⟨mem_univ _,hsource t.2 ht.2⟩).comp (f := fun x : ℂ × E => (x.1,L x.2)) hJ

end NLS.ComplexAnalysis
