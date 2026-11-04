import NLS.KdV.HillEnergyDifferentialCompactTransport
import NLS.KdV.HillSourceMidpointGapContinuity
import NLS.ZakharovShabat.SourceIsolatingUniformPoleBounds

/-! Every positive ORIGINAL patch circle lies strictly to the right
of zero at a real physical source. The actual central gap contains the
balanced zero frequency; quantitative disc separation excludes zero
from every positive closed disc. This works BEFORE ALL positive rows. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem zero_mem_central_disc_of_real (P : HillProductEquationPatch) (q : PeriodOneHminusOne)
    (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) : (0:ℂ) ∈ P.discs 0 := by
  have h := (P.actual_real_graph_mem q hq hr 1).1.2 0
  change hillIndependentFrequency ((P.parent.parent.miuraBall.actionBall.shift:ℂ),hillHminusPsiZeroDisplacement 1 ⟨q,hr⟩) 0 ∈ P.discs 0 at h
  rwa [hillIndependentFrequency_zero] at h

theorem positive_circle_left_of_real (P : HillProductEquationPatch) (q : PeriodOneHminusOne)
    (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) (m : ℕ+) :
    0 < P.centers ((m:ℕ):ℤ)-P.radii ((m:ℕ):ℤ) := by
  let k : ℤ := ((m:ℕ):ℤ)
  let a := P.centers k
  let R := P.radii k
  let ξ := canonicalPeriodicLeft (by norm_num) (by norm_num) (periodOnePotential (P.sourcePsi q)) (periodOnePotential_mem _) k
  let B := P.parent.parent.miuraBall.actionBall
  let u : PeriodOneRealL2 := ⟨B.lift q,B.lift_real q (P.parent.subset (P.subset hq)).1 hr⟩
  have hξpos : 0 < ξ.re := hillMiura_positive_gap_left_pos u k (by dsimp only [k]; exact_mod_cast m.pos)
  have hξ : ξ ∈ P.discs k := P.isolating.gap (P.sourcePsi q) (P.image q hq).2 k (left_mem_segment ℝ _ _)
  have hupper : ξ.re < a+R := by
    rw [P.discs_eq] at hξ
    exact (re_bounds_of_mem_realCenteredBall hξ).2
  have hC : 0 < P.separation⁻¹ := inv_pos.mpr (zero_lt_one.trans_le P.isolating.one_le)
  by_contra hnot
  have haR : a ≤ R := by change ¬ 0 < a-R at hnot; linarith
  have hzero : (0:ℂ) ∈ closure (P.discs k) := by
    rw [P.discs_eq,closure_ball _ (P.radii_pos k).ne',mem_closedBall,dist_eq_norm]
    simp only [zero_sub,norm_neg,Complex.norm_real,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith,haR⟩
  have hs := P.isolating.uniform_pole_distance k 0 (by dsimp only [k]; exact_mod_cast m.ne_zero)
    0 hzero 0 (P.zero_mem_central_disc_of_real q hq hr)
  have hs0 : P.separation⁻¹ ≤ 0 := by simpa only [sub_self,norm_zero] using hs
  exact (not_le_of_gt hC) hs0

end NLS.KdV.HillProductEquationPatch
