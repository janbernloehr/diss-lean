import NLS.KdV.HillProductEquationDiagonalLimit
import NLS.KdV.HillWeightedColumnUniformGapTail

/-! One high-row cutoff controls every actual real Hill period
Jacobian diagonal, BEFORE ALL positive numerator indices. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem sequenceJacobian_actual_real_uniform_diagonal_tail (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n m : ℕ+, N ≤ (m:ℕ) →
      ‖P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) (lp.single 2 m 1) m-1‖ < ε := by
  let B := P.parent.parent.miuraBall.actionBall
  have hb := (P.parent.subset (P.subset hq)).1
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q hb hr⟩
  have hreal : IsRealType (CoeffPair.toMax 2 (P.sourcePsi q)) := (hillMiuraRealSource u).property
  obtain ⟨N,hN⟩ := hillWeightedColumnGapNumerator_uniform_gap_tail P.isolating (P.sourcePsi q)
    (P.image q hq).2 hreal ε hε
  refine ⟨N,?_⟩
  intro n m hm
  let d := hillHminusPsiZeroDisplacement n ⟨q,hr⟩
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos ((m:ℕ):ℤ)) (P.discs_eq ((m:ℕ):ℤ))
  rw [P.sequenceJacobian_coordinate n m m d q (P.actual_real_graph_mem q hq hr n) D rfl rfl]
  by_cases hmn : m = n
  · rw [if_pos hmn,if_pos hmn.symm,sub_self,norm_zero]
    exact hε
  · rw [if_neg hmn]
    obtain ⟨z,hz,hcol⟩ := hillEnergyProductPeriodColumn_real_mean_value n m (B.shift:ℂ) (P.sourcePsi q) hreal
      ((m:ℕ):ℤ) d D (fun z hz => hillProductColumnGapNumerator_actual_real n m ⟨q,hr⟩ u B.shift
        (B.image q hb) (B.outside q hb) D z hz)
    rw [hcol]
    have he (A E : ℂ) : A*(-E)-1 = -(A*E+1) := by ring
    rw [he,norm_neg]
    exact hN (B.shift:ℂ) d
      (fun k => P.parent.actual_independentFrequency_mem_signed_gap n q (P.subset hq) hr k) n m hm hmn z hz

theorem sequenceJacobian_actual_real_uniform_high_diagonal_lower (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ N : ℕ, ∀ n m : ℕ+, N ≤ (m:ℕ) →
      (1/2:ℝ) ≤ ‖P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) (lp.single 2 m 1) m‖ := by
  obtain ⟨N,hN⟩ := P.sequenceJacobian_actual_real_uniform_diagonal_tail q hq hr (1/2) (by norm_num)
  refine ⟨N,?_⟩
  intro n m hm
  have he := hN n m hm
  have ht := norm_le_norm_sub_add (1:ℂ)
    (P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) (lp.single 2 m 1) m)
  rw [norm_one,norm_sub_rev] at ht
  linarith

end NLS.KdV.HillProductEquationPatch
