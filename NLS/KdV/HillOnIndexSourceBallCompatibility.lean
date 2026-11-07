import NLS.KdV.HillOnIndexRealPatchCompatibility
import NLS.KdV.HillPhysicalAbelianSourceBalls

/-! WHOLE complex source-ball overlap compatibility of the ACTUAL
diagonal Cartesian factors, for arbitrary Miura patches and shifts.
The real-centered source balls are fixed BEFORE ALL indices. -/
noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV.HillPhysicalAbelianSourceBall

def diagonalPlus (B : HillPhysicalAbelianSourceBall) (n : ℕ+) : PeriodOneHminusOne → ℂ := B.patch.physicalOnIndexCartesianPlus n

def diagonalMinus (B : HillPhysicalAbelianSourceBall) (n : ℕ+) : PeriodOneHminusOne → ℂ := B.patch.physicalOnIndexCartesianMinus n

theorem analytic_diagonalPlus (B : HillPhysicalAbelianSourceBall) (n : ℕ+) :
    AnalyticOnNhd ℂ (B.diagonalPlus n) B.source := (B.patch.analytic_physicalOnIndexCartesianPlus n).mono B.subset

theorem analytic_diagonalMinus (B : HillPhysicalAbelianSourceBall) (n : ℕ+) :
    AnalyticOnNhd ℂ (B.diagonalMinus n) B.source := (B.patch.analytic_physicalOnIndexCartesianMinus n).mono B.subset

theorem diagonalPlus_eq_on_overlap (B C : HillPhysicalAbelianSourceBall) (n : ℕ+) :
    EqOn (B.diagonalPlus n) (C.diagonalPlus n) (B.source ∩ C.source) := by
  intro q hq
  have hreal : ∃ a ∈ B.source ∩ C.source, IsRealPeriodOneHminusOne a :=
    exists_real_mem_periodOneHminus_ball_inter B.center C.center B.center_real C.center_real B.radius C.radius ⟨q,hq⟩
  exact analytic_eqOn_of_real_periodOneHminus _ (B.source_open.inter C.source_open)
    ((convex_ball B.center B.radius).inter (convex_ball C.center C.radius)).isPreconnected hreal _ _
    ((B.analytic_diagonalPlus n).mono inter_subset_left) ((C.analytic_diagonalPlus n).mono inter_subset_right)
    (fun a ha har => (B.patch.physicalOnIndexCartesian_eq_of_real_overlap C.patch n a
      (B.subset ha.1).1 (C.subset ha.2).1 har).1) hq

theorem diagonalMinus_eq_on_overlap (B C : HillPhysicalAbelianSourceBall) (n : ℕ+) :
    EqOn (B.diagonalMinus n) (C.diagonalMinus n) (B.source ∩ C.source) := by
  intro q hq
  have hreal : ∃ a ∈ B.source ∩ C.source, IsRealPeriodOneHminusOne a :=
    exists_real_mem_periodOneHminus_ball_inter B.center C.center B.center_real C.center_real B.radius C.radius ⟨q,hq⟩
  exact analytic_eqOn_of_real_periodOneHminus _ (B.source_open.inter C.source_open)
    ((convex_ball B.center B.radius).inter (convex_ball C.center C.radius)).isPreconnected hreal _ _
    ((B.analytic_diagonalMinus n).mono inter_subset_left) ((C.analytic_diagonalMinus n).mono inter_subset_right)
    (fun a ha har => (B.patch.physicalOnIndexCartesian_eq_of_real_overlap C.patch n a
      (B.subset ha.1).1 (C.subset ha.2).1 har).2) hq

end NLS.KdV.HillPhysicalAbelianSourceBall
