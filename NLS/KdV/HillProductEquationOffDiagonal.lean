import NLS.KdV.HillProductEquationRealDiagonal
import NLS.KdV.HillRealOffDiagonalPeriods
import NLS.ZakharovShabat.SourcePsiGapProductAllDiscBound

/-! The actual full period Jacobians share one off-diagonal kernel
bound before all numerator, row and column indices at each real source. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_actual_real_allDisc_quotient_bound (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ n : ℕ+, ∀ m : ℤ, ∀ z ∈ P.discs m,
      ‖sourceSingleRootQuotientJointProduct (by norm_num) (by norm_num) m
        (z,(hillIndependentFrequencyDisplacement
          ((P.parent.parent.miuraBall.actionBall.shift:ℂ),hillHminusPsiZeroDisplacement n ⟨q,hr⟩),P.sourcePsi q))‖ ≤ Q := by
  obtain ⟨O,_,hO,Q,hQ,hbound⟩ := P.quotients.gap_product_allDisc_quotient_bound P.isolating P.V_open
    (P.sourcePsi q) (P.image q hq).1 (P.image q hq).2
  refine ⟨Q,hQ,?_⟩
  intro n m z hz
  apply hbound (P.sourcePsi q) hO _ ?_ m z hz
  intro k
  exact P.parent.actual_independentFrequency_mem_signed_gap n q (P.subset hq) hr k

theorem exists_uniform_actual_real_off_diagonal_bound (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n m r : ℕ+, r ≠ m →
      ‖P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) (lp.single 2 r 1) m‖ ≤
        ‖hillHminusGapWidthDisplacement ⟨q,hr⟩ m‖*K*‖hillFreeInteractionKernel m ((r:ℕ):ℤ)‖ := by
  obtain ⟨Q,hQ,hquot⟩ := P.exists_actual_real_allDisc_quotient_bound q hq hr
  let K := 2*Real.pi^5*P.separation^5*Q
  have hc : 0 ≤ P.separation := zero_le_one.trans P.isolating.one_le
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K,hK,?_⟩
  intro n m r hrm
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos ((m:ℕ):ℤ)) (P.discs_eq ((m:ℕ):ℤ))
  rw [P.sequenceJacobian_coordinate n m r _ q (P.actual_real_graph_mem q hq hr n) D rfl rfl]
  by_cases hmn : m = n
  · have hnr : n ≠ r := by intro h; exact hrm (h.symm.trans hmn.symm)
    rw [if_pos hmn,if_neg hnr,norm_zero]
    positivity
  · rw [if_neg hmn]
    by_cases hrn : r = n
    · rw [hrn]
      have hz : hillEnergyProductPeriodColumn n n (P.parent.parent.miuraBall.actionBall.shift:ℂ)
          (P.sourcePsi q) D (hillHminusPsiZeroDisplacement n ⟨q,hr⟩) = 0 := by
        simp [hillEnergyProductPeriodColumn,hillEnergyProductCoordinateDerivative_omitted,circleIntegral]
      rw [hz,mul_zero,norm_zero]
      exact mul_nonneg (mul_nonneg (norm_nonneg _) hK) (norm_nonneg _)
    · let B := P.parent.parent.miuraBall.actionBall
      have hb := (P.parent.subset (P.subset hq)).1
      let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q hb hr⟩
      apply hillWeightedProductPeriodColumn_actual_off_diagonal_bound P.isolating ⟨q,hr⟩ u B.shift
        (B.image q hb) (B.outside q hb) (P.image q hq).2 n m r hmn hrn hrm
        (fun k => P.isolating.gap (P.sourcePsi q) (P.image q hq).2 k
          (P.parent.actual_independentFrequency_mem_signed_gap n q (P.subset hq) hr k))
        (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos ((m:ℕ):ℤ)) (P.discs_eq ((m:ℕ):ℤ)) Q
      exact hquot n ((m:ℕ):ℤ)

end NLS.KdV.HillProductEquationPatch
