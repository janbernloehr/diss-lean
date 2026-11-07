import NLS.KdV.HillProductEquationCompactBounds
import NLS.KdV.HillProductEquationDerivative
import NLS.ComplexAnalysis.BanachHolomorphicC1

/-! A single FULL operator-norm Lipschitz bound for the ACTUAL Hill
period data Jacobians near ALL original real gap-data centers and
BEFORE ALL numerator indices. -/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_uniform_joint_sequenceJacobian_Lipschitz (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
      ∀ d ∈ hillHminusEnergyGapData ⟨q,hr⟩,
        ball (d,q) r ⊆ P.inputDomain ∧
        ∀ n : ℕ+, ∀ t ∈ ball (d,q) r, ∀ s ∈ ball (d,q) r,
          ‖P.sequenceJacobian n t-P.sequenceJacobian n s‖ ≤ C*‖t-s‖ := by
  obtain ⟨R,L,hR,hL,hballs⟩ := P.exists_actual_real_uniform_equation_balls q hq hr
  let r := R/4
  have hrpos : 0 < r := by dsimp only [r]; positivity
  have hfour : 4*r = R := by dsimp only [r]; ring
  let C := 4*L/r^2
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨r,C,hrpos,hC,?_⟩
  intro d hd
  have hRU : ball (d,q) R ⊆ P.inputDomain := ball_subset_closedBall.trans (hballs d hd).1
  have hrR : r ≤ R := by dsimp only [r]; linarith
  refine ⟨(ball_subset_ball hrR).trans hRU,?_⟩
  intro n t ht s hs
  have hder := norm_fderiv_sub_le_of_holomorphic_ball_bound (P.equation n) (d,q) r L hrpos
    (by rw [hfour]; exact ((P.analytic_equation n).mono hRU).differentiableOn)
    (by rw [hfour]; exact fun z hz => (hballs d hd).2 n z (ball_subset_closedBall hz)) hs ht
  change ‖(fderiv ℂ (P.equation n) t).comp _-(fderiv ℂ (P.equation n) s).comp _‖ ≤ _
  rw [← ContinuousLinearMap.sub_comp]
  calc
    _ ≤ ‖fderiv ℂ (P.equation n) t-fderiv ℂ (P.equation n) s‖*
        ‖ContinuousLinearMap.inl ℂ (lp (fun _ : ℕ+ => ℂ) 2) PeriodOneHminusOne‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℂ (P.equation n) t-fderiv ℂ (P.equation n) s‖*1 :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inl_le_one ℂ _ _) (norm_nonneg _)
    _ ≤ C*‖t-s‖ := by simpa only [mul_one] using hder

end NLS.KdV.HillProductEquationPatch
