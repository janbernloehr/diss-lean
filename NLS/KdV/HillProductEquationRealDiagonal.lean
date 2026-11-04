import NLS.KdV.HillProductEquationDerivative
import NLS.KdV.HillProductRealGapColumns

/-! Every diagonal entry of the ACTUAL bounded Hill period Jacobian is
nonzero at the actual original real zero sequence. This includes the
omitted midpoint row and all low or collapsed gaps. Off-diagonal entries
remain present; no operator invertibility is asserted. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillPeriodEquationWeight_ne_zero (n m : ℕ+) (hmn : m ≠ n) :
    hillPeriodEquationWeight n m ≠ 0 := by
  unfold hillPeriodEquationWeight
  exact mul_ne_zero (by simp [Real.pi_ne_zero])
    (div_ne_zero (sub_ne_zero.mpr (pnat_complex_squares_ne hmn.symm))
      (pow_ne_zero 2 (by exact_mod_cast n.ne_zero)))

namespace HillProductEquationPatch

theorem sequenceJacobian_actual_real_diagonal_ne_zero (P : HillProductEquationPatch)
    (n m : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.source)
    (hr : IsRealPeriodOneHminusOne q) :
    P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) (lp.single 2 m 1) m ≠ 0 := by
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos ((m:ℕ):ℤ)) (P.discs_eq ((m:ℕ):ℤ))
  rw [P.sequenceJacobian_coordinate n m m _ q (P.actual_real_graph_mem q hq hr n) D rfl rfl]
  by_cases hmn : m = n
  · simp only [hmn,if_pos,ne_eq,one_ne_zero,not_false_eq_true]
  · rw [if_neg hmn]
    apply mul_ne_zero (hillPeriodEquationWeight_ne_zero n m hmn)
    let B := P.parent.parent.miuraBall.actionBall
    have hb := (P.parent.subset (P.subset hq)).1
    let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q hb hr⟩
    exact hillEnergyProductPeriodColumn_actual_diagonal_ne_zero n m hmn ⟨q,hr⟩ u B.shift
      (B.image q hb) (B.outside q hb) D

end HillProductEquationPatch
end NLS.KdV
