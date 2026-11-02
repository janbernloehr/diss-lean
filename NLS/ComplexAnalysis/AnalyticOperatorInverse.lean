import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Complex.Basic

/-! # Analytic inversion of an operator family equal to the identity at zero -/
noncomputable section
open Set Metric Filter Topology
namespace NLS.ComplexAnalysis
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem exists_analytic_operator_inverse_near_zero
    (T : E → (F →L[ℂ] F)) (W : Set E) (hW : IsOpen W) (h0W : 0 ∈ W)
    (hTa : AnalyticOnNhd ℂ T W) (hT0 : T 0 = ContinuousLinearMap.id ℂ F) :
    ∃ V : Set E, ∃ R : E → (F →L[ℂ] F), V ⊆ W ∧ IsOpen V ∧ 0 ∈ V ∧
      AnalyticOnNhd ℂ R V ∧ R 0 = ContinuousLinearMap.id ℂ F ∧
      ∀ q ∈ V, (T q).comp (R q) = ContinuousLinearMap.id ℂ F ∧
        (R q).comp (T q) = ContinuousLinearMap.id ℂ F ∧ ‖R q‖ ≤ 2 := by
  have hnear : ∀ᶠ q in 𝓝 (0 : E), ‖T q-ContinuousLinearMap.id ℂ F‖ < 1 := by
    have hc := ((hTa 0 h0W).sub (analyticAt_const (v := ContinuousLinearMap.id ℂ F))).continuousAt.norm
    exact hc.eventually (gt_mem_nhds (by
      change ‖T 0-ContinuousLinearMap.id ℂ F‖ < 1
      rw [hT0,sub_self,norm_zero]
      norm_num))
  obtain ⟨U,hUsub,hU,h0U⟩ := _root_.mem_nhds_iff.mp hnear
  let V := W ∩ U
  have hV : IsOpen V := hW.inter hU
  have h0V : (0 : E) ∈ V := ⟨h0W,h0U⟩
  have hu (q : E) (hq : q ∈ V) : IsUnit (T q) := by
    have hs : ‖(1 : F →L[ℂ] F)-T q‖ < 1 := by
      rw [norm_sub_rev]
      exact hUsub hq.2
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hs
  let R := fun q => Ring.inverse (T q)
  have hRa : AnalyticOnNhd ℂ R V := by
    intro q hq
    exact (analyticOnNhd_inverse (T q) (hu q hq)).comp (hTa q hq.1)
  have hR0 : R 0 = ContinuousLinearMap.id ℂ F := by
    dsimp only [R]
    rw [hT0]
    exact Ring.inverse_one _
  have hRsmall : ∀ᶠ q in 𝓝 (0 : E), ‖R q‖ < 2 :=
    (hRa 0 h0V).continuousAt.norm.eventually (gt_mem_nhds (by
      change ‖R 0‖ < 2
      rw [hR0]
      linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := F)]))
  obtain ⟨B,hBsub,hB,h0B⟩ := _root_.mem_nhds_iff.mp hRsmall
  refine ⟨V ∩ B,R,fun _ hq => hq.1.1,hV.inter hB,⟨h0V,h0B⟩,
    hRa.mono inter_subset_left,hR0,?_⟩
  intro q hq
  exact ⟨Ring.mul_inverse_cancel _ (hu q hq.1),Ring.inverse_mul_cancel _ (hu q hq.1),
    (hBsub hq.2).le⟩

end NLS.ComplexAnalysis
