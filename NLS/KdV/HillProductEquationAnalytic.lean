import NLS.KdV.HillProductEquationLocalBounds
import NLS.SequenceSpaces.PositiveCoordinateAnalytic

/-! The ACTUAL full source-joint nonlinear Hill period equation is
Banach analytic on ONE common open placed-input domain before ALL n.
All actual real zero-sequence graphs lie there and solve the equation. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem analytic_equation (P : HillProductEquationPatch) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.equation n) P.inputDomain := by
  intro t ht
  obtain ⟨J,hJ,htJ,hJD,L,_,hbound⟩ := P.exists_local_uniform_equation_bound t ht
  have hcoord (m : ℕ+) : AnalyticOnNhd ℂ (fun s => P.equation n s m) J := by
    apply ((P.analytic_row n m).mono (fun s hs => ⟨mem_univ _,(hJD hs).2⟩)).congr hJ
    intro s hs
    exact (P.equation_apply n m s (hJD hs)).symm
  exact (LpSequence.analyticOnNhd_positiveL2_of_bounded_coordinatewise (P.equation n)
    hJ hcoord L (hbound n)) t htJ

theorem equation_actual_real_zeros (P : HillProductEquationPatch) (n : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    P.equation n (hillHminusPsiZeroDisplacement n ⟨q,hr⟩,q) = 0 := by
  ext m
  rw [P.equation_apply n m _ (P.actual_real_graph_mem q hq hr n),P.row_eq_native]
  exact P.parent.productEquationRow_actual_real_zeros n m q (P.subset hq) hr
    (P.isolating.periodCircle (P.sourcePsi q) (P.image q hq).2 ((m:ℕ):ℤ)
      (P.centers ((m:ℕ):ℤ)) (P.radii ((m:ℕ):ℤ)) (P.radii_pos _) (P.discs_eq _))

end NLS.KdV.HillProductEquationPatch
