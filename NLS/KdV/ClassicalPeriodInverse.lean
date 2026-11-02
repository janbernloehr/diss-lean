import NLS.KdV.ClassicalPeriodOperator
import Mathlib.Analysis.Normed.Operator.Banach

/-! # An actual analytic inverse of the infinite Hill period operator

Operator-norm analyticity and the exact free identity give the Neumann
neighborhood. Ring inversion is analytic there and supplies both inverse
identities. No pointwise invertibility or inverse selection is assumed.
-/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.KdV

theorem exists_classicalHill_analytic_period_inverse :
    ∃ N : ℕ, ∃ V : Set (NLS.LinearVolterra.Curve ℂ),
      ∃ T R : NLS.LinearVolterra.Curve ℂ → (NLS.Coeff 2 →L[ℂ] NLS.Coeff 2),
        0 < N ∧ IsOpen V ∧ 0 ∈ V ∧ AnalyticOnNhd ℂ T V ∧ AnalyticOnNhd ℂ R V ∧
        T 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
        R 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
        (∀ q ∈ V, (T q).comp (R q) = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧
          (R q).comp (T q) = ContinuousLinearMap.id ℂ (NLS.Coeff 2) ∧ ‖R q‖ ≤ 2) ∧
        (∀ q ∈ V, ∀ m n : ℤ, (T q (lp.single 2 n 1)) m = classicalHillPeriodMatrix N q m n) ∧
        ∃ A : ℝ, ClassicalAllContourPeriodData N V A := by
  obtain ⟨N,W,C,T,hN,hW,h0W,hC,hTa,_,hentry,_,hT0,A,D⟩ :=
    exists_classicalHill_analytic_period_operator
  have hnear : ∀ᶠ q in 𝓝 (0 : NLS.LinearVolterra.Curve ℂ),
      ‖T q-ContinuousLinearMap.id ℂ (NLS.Coeff 2)‖ < 1 := by
    have hc := ((hTa 0 h0W).sub (analyticAt_const (v := ContinuousLinearMap.id ℂ (NLS.Coeff 2)))).continuousAt.norm
    exact hc.eventually (gt_mem_nhds (by
      change ‖T 0-ContinuousLinearMap.id ℂ (NLS.Coeff 2)‖ < 1
      rw [hT0,sub_self,norm_zero]
      norm_num))
  obtain ⟨U,hUsub,hU,h0U⟩ := _root_.mem_nhds_iff.mp hnear
  let V := W ∩ U
  have hV : IsOpen V := hW.inter hU
  have h0V : (0 : NLS.LinearVolterra.Curve ℂ) ∈ V := ⟨h0W,h0U⟩
  have hu (q : NLS.LinearVolterra.Curve ℂ) (hq : q ∈ V) : IsUnit (T q) := by
    have hs : ‖(1 : NLS.Coeff 2 →L[ℂ] NLS.Coeff 2)-T q‖ < 1 := by
      rw [norm_sub_rev]
      exact hUsub hq.2
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hs
  let R := fun q => Ring.inverse (T q)
  have hRa : AnalyticOnNhd ℂ R V := by
    intro q hq
    exact (analyticOnNhd_inverse (T q) (hu q hq)).comp (hTa q hq.1)
  have hR0 : R 0 = ContinuousLinearMap.id ℂ (NLS.Coeff 2) := by
    dsimp only [R]
    rw [hT0]
    exact Ring.inverse_one _
  have hRsmall : ∀ᶠ q in 𝓝 (0 : NLS.LinearVolterra.Curve ℂ), ‖R q‖ < 2 :=
    (hRa 0 h0V).continuousAt.norm.eventually (gt_mem_nhds (by
      change ‖R 0‖ < 2
      rw [hR0]
      linarith [ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := NLS.Coeff 2)]))
  obtain ⟨B,hBsub,hB,h0B⟩ := _root_.mem_nhds_iff.mp hRsmall
  refine ⟨N,V ∩ B,T,R,hN,hV.inter hB,⟨h0V,h0B⟩,
    hTa.mono (fun _ hq => hq.1.1),hRa.mono inter_subset_left,hT0,hR0,?_,?_,
    A,D.mono (fun _ hq => hq.1.1) (hV.inter hB) ⟨h0V,h0B⟩⟩
  · intro q hq
    exact ⟨Ring.mul_inverse_cancel _ (hu q hq.1),Ring.inverse_mul_cancel _ (hu q hq.1),
      (hBsub hq.2).le⟩
  intro q hq m n
  exact hentry q hq.1.1 m n

end NLS.KdV
