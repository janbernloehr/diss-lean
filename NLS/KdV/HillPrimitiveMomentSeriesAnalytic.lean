import NLS.KdV.HillPrimitiveMomentSeriesLocalBound

/-! Full Banach-source analyticity of the actual l1 moment rows and
their literal infinite weighted sums on the common complex source. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

theorem analytic_centeredSecondMomentRow (P : HillProductEquationPatch)
    (D : MomentSeriesNeighborhood P) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.centeredSecondMomentRow D.ambient n) D.source := by
  apply Coeff.analyticOnNhd_positiveSummableRealization
  · exact P.analytic_normalizedWeightedSecondMoment D n
  · exact P.summable_normalizedWeightedSecondMoment D n
  · exact P.exists_local_normalizedWeightedSecondMoment_sum_bound D n

theorem analytic_centeredSecondMomentSeries (P : HillProductEquationPatch)
    (D : MomentSeriesNeighborhood P) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.centeredSecondMomentSeries D.ambient n) D.source := by
  intro q hq
  have hs := ((lp.tsumCLM ℂ ℤ ℂ).analyticAt _).comp
    (f := P.centeredSecondMomentRow D.ambient n) (P.analytic_centeredSecondMomentRow D n q hq)
  have ha : AnalyticAt ℂ (fun a : PeriodOneHminusOne =>
      (2*Real.pi:ℂ)*(∑' k : ℤ, P.centeredSecondMomentRow D.ambient n a k)) q :=
    analyticAt_const.mul hs
  apply ha.congr
  filter_upwards [D.source_open.mem_nhds hq] with a ha
  exact (P.centeredSecondMomentSeries_eq_row_sum D n a ha).symm

theorem centeredSecondMomentSeries_independent_primitive_neighborhood (P : HillProductEquationPatch)
    {W V : Set (CoeffPair 2)}
    (C : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) W)
    (E : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) V)
    (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ P.momentSource C ∩ P.momentSource E) :
    P.centeredSecondMomentSeries W n q=P.centeredSecondMomentSeries V n q := by
  apply tsum_congr
  intro m
  rw [P.centeredMoment_independent_primitive_neighborhood C E n m 1 q hq]

end NLS.KdV.HillProductEquationPatch
