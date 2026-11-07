import NLS.KdV.HillCommonSimpleComplexZeroDomain

/-! The common FULL-l2 zero sequences agree with the previously proved
individual retained simple-root complexifications on their ENTIRE
complex overlaps. The original labelled roots are reused consistently. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal Classical
namespace NLS.KdV

theorem HillHminusPsiZeroBall.canonical_sequence_energy_eq {n m : ℕ+}
    (C : HillHminusPsiZeroBall n m) (q : PeriodOneHminusOne) (hC : q ∈ C.source)
    (hq : q ∈ hillHminusCanonicalZeroSequenceDomain) :
    hillEnergySequenceZero m (hillHminusCanonicalZeroSequence n q) = C.value q := by
  obtain ⟨B,hB⟩ := mem_iUnion.mp hq
  let f : PeriodOneHminusOne → ℂ := fun a => hillEnergySequenceZero m (B.value n a)
  have hf : AnalyticOnNhd ℂ f B.source := by
    intro a ha
    have he := ((lp.evalCLM ℂ (fun _ : ℕ+ => ℂ) 2 m).analyticAt _).comp (B.analytic_value n a ha)
    exact analyticAt_const.add (analyticAt_const.mul he)
  have hreal : ∃ a ∈ B.source ∩ C.source, IsRealPeriodOneHminusOne a :=
    exists_real_mem_periodOneHminus_ball_inter B.center C.center B.center_real C.center_real
      B.radius C.radius ⟨q,hB,hC⟩
  have he := analytic_eqOn_of_real_periodOneHminus _ (B.source_open.inter C.source_open)
    ((convex_ball B.center B.radius).inter (convex_ball C.center C.radius)).isPreconnected hreal f C.value
    (hf.mono inter_subset_left) (C.analytic_value.mono inter_subset_right) (by
      intro a ha har
      dsimp only [f]
      rw [B.real_eq n a ha.1 har,hillEnergySequenceZero_real,C.real_eq a ha.2 har])
  rw [B.canonical_value_eq n q hB]
  exact he ⟨hB,hC⟩

theorem hillHminusCanonicalZeroSequence_eq_retained_pair_root (n m : ℕ+)
    (q : PeriodOneHminusOne) (hq : q ∈ hillHminusCanonicalZeroSequenceDomain)
    (hm : q ∈ hillHminusPsiZeroDomain n m) :
    hillEnergySequenceZero m (hillHminusCanonicalZeroSequence n q) = hillHminusCanonicalRetainedPsiZero n m q := by
  obtain ⟨C,hC⟩ := mem_iUnion.mp hm
  rw [C.canonical_zero_eq q hC]
  exact C.canonical_sequence_energy_eq q hC hq

end NLS.KdV
