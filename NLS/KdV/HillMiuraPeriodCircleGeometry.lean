import NLS.KdV.HillMiuraPositiveGaps
import NLS.ZakharovShabat.SourceCriticalRootPeriodCircle

noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

/-- Every actual period circle around a real Miura gap lies strictly
between the neighboring endpoint slots; no shrinking assumption is needed. -/
theorem miuraPeriodCircle_adjacent_bounds (u : PeriodOneRealL2) (m : ℤ)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) m) :
    (hillMiuraDiracRight u.val (m-1)).re<D.center-D.radius ∧
      D.center+D.radius<(hillMiuraDiracLeft u.val (m+1)).re := by
  have hleft : hillMiuraDiracLeft u.val m∈ball (D.center:ℂ) D.radius :=
    D.gap (left_mem_segment ℝ _ _)
  have hright : hillMiuraDiracRight u.val m∈ball (D.center:ℂ) D.radius :=
    D.gap (right_mem_segment ℝ _ _)
  have hl := re_bounds_of_mem_realCenteredClosedBall (ball_subset_closedBall hleft)
  have hr := re_bounds_of_mem_realCenteredClosedBall (ball_subset_closedBall hright)
  have hsep {i j : ℤ} (hij : i<j) :
      (hillMiuraDiracRight u.val i).re<(hillMiuraDiracLeft u.val j).re :=
    canonicalPeriodicRight_re_lt_left_of_lt (by norm_num) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)
      (isRealType_periodOnePotential _ (hillMiuraRealSource u).property) hij
  constructor
  · rcases D.other (m-1) (by omega) (hillMiuraDiracRight u.val (m-1))
      (right_mem_segment ℝ _ _) with h | h
    · exact h
    · have hs := hsep (show m-1<m by omega)
      change (hillMiuraDiracRight u.val (m-1)).re<(hillMiuraDiracLeft u.val m).re at hs
      linarith
  · rcases D.other (m+1) (by omega) (hillMiuraDiracLeft u.val (m+1))
      (left_mem_segment ℝ _ _) with h | h
    · have hs := hsep (show m<m+1 by omega)
      change (hillMiuraDiracRight u.val m).re<(hillMiuraDiracLeft u.val (m+1)).re at hs
      linarith
    · exact h

/-- Every positive-index real Miura period circle is wholly in the
positive frequency half-plane, including circles around collapsed gaps. -/
theorem miuraPeriodCircle_left_pos (u : PeriodOneRealL2) (m : ℕ+)
    (D : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
      (hillMiuraDiagonal u.val) ((m:ℕ):ℤ)) : 0<D.center-D.radius := by
  have hb := (miuraPeriodCircle_adjacent_bounds u ((m:ℕ):ℤ) D).1
  have hzero := (hillMiura_gap_zero_contains_zero u).2
  change 0≤(hillMiuraDiracRight u.val 0).re at hzero
  have hm : (0:ℤ)≤((m:ℕ):ℤ)-1 := by have := m.pos; omega
  rcases eq_or_lt_of_le hm with he | he
  · rw [←he] at hb
    exact hzero.trans_lt hb
  · have hs := canonicalPeriodicRight_re_lt_left_of_lt (by norm_num) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)
      (isRealType_periodOnePotential _ (hillMiuraRealSource u).property) he
    have ho := hillMiuraDiracPair_ordered u.val (((m:ℕ):ℤ)-1)
    change (hillMiuraDiracRight u.val 0).re<(hillMiuraDiracLeft u.val (((m:ℕ):ℤ)-1)).re at hs
    linarith

end NLS.KdV
