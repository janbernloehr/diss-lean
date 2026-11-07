import NLS.KdV.HillProductEquationOffDiagonal
import NLS.KdV.HillWeightedColumnNumeratorBound

/-! One upper norm bound controls EVERY actual real Hill period
Jacobian diagonal, before all numerator and row indices. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem exists_actual_real_uniform_diagonal_upper (P : HillProductEquationPatch)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n m : ℕ+,
      ‖P.sequenceJacobian n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) (lp.single 2 m 1) m‖ ≤ M := by
  obtain ⟨Q,hQ,hquot⟩ := P.exists_actual_real_allDisc_quotient_bound q hq hr
  refine ⟨max 1 (2*Real.pi^3*P.separation^3*Q),zero_le_one.trans (le_max_left _ _),?_⟩
  intro n m
  let B := P.parent.parent.miuraBall.actionBall
  have hb := (P.parent.subset (P.subset hq)).1
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q hb hr⟩
  have hreal : IsRealType (CoeffPair.toMax 2 (P.sourcePsi q)) := (hillMiuraRealSource u).property
  let d := hillHminusPsiZeroDisplacement n ⟨q,hr⟩
  let D := P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
    (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos ((m:ℕ):ℤ)) (P.discs_eq ((m:ℕ):ℤ))
  rw [P.sequenceJacobian_coordinate n m m d q (P.actual_real_graph_mem q hq hr n) D rfl rfl]
  by_cases hmn : m = n
  · rw [if_pos hmn,if_pos hmn.symm,norm_one]
    exact le_max_left _ _
  · rw [if_neg hmn]
    obtain ⟨z,hz,hcol⟩ := hillEnergyProductPeriodColumn_real_mean_value n m (B.shift:ℂ) (P.sourcePsi q) hreal
      ((m:ℕ):ℤ) d D (fun z hz => hillProductColumnGapNumerator_actual_real n m ⟨q,hr⟩ u B.shift
        (B.image q hb) (B.outside q hb) D z hz)
    rw [hcol,mul_neg,norm_neg]
    have hplace (k : ℤ) : hillIndependentFrequency ((B.shift:ℂ),d) k ∈ P.discs k :=
      P.isolating.gap (P.sourcePsi q) (P.image q hq).2 k
        (P.parent.actual_independentFrequency_mem_signed_gap n q (P.subset hq) hr k)
    have hzD := P.isolating.gap (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ) hz
    have hother : z ∈ sourceStandardRootOmittedDomain (by norm_num) (by norm_num) (P.sourcePsi q) ((m:ℕ):ℤ) := by
      intro k hkm hzk
      exact Set.disjoint_left.mp (P.isolating.disjoint ((m:ℕ):ℤ) k hkm.symm) hzD
        (P.isolating.gap (P.sourcePsi q) (P.image q hq).2 k hzk)
    exact (hillWeightedColumnGapNumerator_bound P.isolating (P.sourcePsi q) (B.shift:ℂ) d
      hplace n m hmn z (subset_closure hzD) hother Q (hquot n ((m:ℕ):ℤ) z hzD)).trans (le_max_right _ _)

end NLS.KdV.HillProductEquationPatch
