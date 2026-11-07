import NLS.KdV.HillProductEquationInvertibleDiagonal
import NLS.KdV.HillWeightedColumnUniformGapLower

/-! The original real Hill period Jacobians have diagonal inverses with
one norm bound before ALL numerator indices. This does not assert a
uniform bound for the full Jacobian inverses. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem sequenceJacobian_actual_real_uniform_diagonal_lower (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n m : ℕ+,
      δ ≤ ‖P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) (lp.single 2 m 1) m‖ := by
  let B := P.parent.parent.miuraBall.actionBall
  have hb := (P.parent.subset (P.subset hq)).1
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q hb hr⟩
  have hreal : IsRealType (CoeffPair.toMax 2 (P.sourcePsi q)) :=
    (hillMiuraRealSource u).property
  obtain ⟨δ,hδ,hbound⟩ := hillWeightedColumnGapNumerator_uniform_gap_lower P.isolating (P.sourcePsi q)
    (P.image q hq).2 hreal
  refine ⟨min 1 δ,lt_min (by norm_num) hδ,?_⟩
  intro n m
  let d := hillHminusPsiZeroDisplacement n ⟨q,hr⟩
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos ((m:ℕ):ℤ)) (P.discs_eq ((m:ℕ):ℤ))
  rw [P.sequenceJacobian_coordinate n m m d q (P.actual_real_graph_mem q hq hr n) D rfl rfl]
  by_cases hmn : m = n
  · rw [if_pos hmn,if_pos hmn.symm,norm_one]
    exact min_le_left _ _
  · rw [if_neg hmn]
    obtain ⟨z,hz,hcol⟩ := hillEnergyProductPeriodColumn_real_mean_value n m (B.shift:ℂ) (P.sourcePsi q) hreal
      ((m:ℕ):ℤ) d D (fun z hz => hillProductColumnGapNumerator_actual_real n m ⟨q,hr⟩ u B.shift
        (B.image q hb) (B.outside q hb) D z hz)
    rw [hcol,mul_neg,norm_neg]
    exact (min_le_right _ _).trans (hbound (B.shift:ℂ) d
      (fun k => P.parent.actual_independentFrequency_mem_signed_gap n q (P.subset hq) hr k) n m hmn z hz)

theorem exists_actual_real_uniform_diagonal_inverse (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℕ+,
      ∃ D : lp (fun _ : ℕ+ => ℂ) 2 ≃L[ℂ] lp (fun _ : ℕ+ => ℂ) 2,
        D.toContinuousLinearMap = LpSequence.positiveOperatorDiagonal
          (P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q)) ∧
        (∀ a m, D.symm a m =
          (P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) (lp.single 2 m 1) m)⁻¹*a m) ∧
        ‖D.symm.toContinuousLinearMap‖ ≤ M := by
  obtain ⟨δ,hδ,hlower⟩ := P.sequenceJacobian_actual_real_uniform_diagonal_lower q hq hr
  refine ⟨δ⁻¹,inv_nonneg.mpr hδ.le,?_⟩
  intro n
  let T := P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q)
  obtain ⟨D,hD,hinv⟩ := LpSequence.exists_positiveOperatorDiagonal_equiv_of_lowerBound T δ hδ (hlower n)
  exact ⟨D,hD,hinv,LpSequence.norm_positive_diagonal_inverse_le T δ hδ (hlower n) D hinv⟩

end NLS.KdV.HillProductEquationPatch
