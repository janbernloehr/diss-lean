import NLS.KdV.HillPrimitiveMomentTailBound
import NLS.SequenceSpaces.PositiveSummableAnalyticAssembly
import NLS.SequenceSpaces.PositiveSquaredGapMomentSummability

/-! Actual local spectral data for the weighted second-moment series.
The tail estimate is constructed around each real original source. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

structure MomentSeriesNeighborhood (P : HillProductEquationPatch) where
  ambient : Set (CoeffPair 2)
  cauchy : SourceFullAbelianUniformCauchyFamily (by simp) (by norm_num) ambient
  source : Set PeriodOneHminusOne
  source_open : IsOpen source
  subset : source ⊆ P.momentSource cauchy
  threshold : ℕ
  constant : ℝ
  constant_pos : 0 < constant
  tail_bound : ∀ a ∈ source, ∀ n m : ℕ+, threshold < (m:ℕ) → m ≠ n →
    ‖(2*Real.pi:ℂ)⁻¹*P.centeredMoment ambient n m 1 a‖ ≤
      constant*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ)‖^2*
        (1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ))

theorem exists_momentSeriesNeighborhood (P : HillProductEquationPatch)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.parent.family.originalDomain
      P.parent.family.domain P.parent.family.roots)
    (q : PeriodOneHminusOne) (hq : q ∈ P.source) (hr : IsRealPeriodOneHminusOne q) :
    ∃ D : MomentSeriesNeighborhood P, q ∈ D.source := by
  obtain ⟨W,C,U,hU,hqU,hUC,K,B,hB,hbound⟩ :=
    P.exists_local_uniform_centeredSecondMoment_tail_bound H q hq hr
  exact ⟨⟨W,C,U,hU,hUC,K,B,hB,hbound⟩,hqU⟩

def normalizedWeightedSecondMoment (P : HillProductEquationPatch) (W : Set (CoeffPair 2))
    (n : ℕ+) (q : PeriodOneHminusOne) (m : ℕ+) : ℂ :=
  ((m:ℕ):ℂ)*((2*Real.pi:ℂ)⁻¹*P.centeredMoment W n m 1 q)

def centeredSecondMomentRow (P : HillProductEquationPatch) (W : Set (CoeffPair 2))
    (n : ℕ+) (q : PeriodOneHminusOne) : Coeff 1 :=
  Coeff.positiveSummableRealization (P.normalizedWeightedSecondMoment W n q)

def centeredSecondMomentSeries (P : HillProductEquationPatch) (W : Set (CoeffPair 2))
    (n : ℕ+) (q : PeriodOneHminusOne) : ℂ :=
  ∑' m : ℕ+, ((m:ℕ):ℂ)*P.centeredMoment W n m 1 q

theorem summable_normalizedWeightedSecondMoment (P : HillProductEquationPatch)
    (D : MomentSeriesNeighborhood P) (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ D.source) :
    Summable (fun m => ‖P.normalizedWeightedSecondMoment D.ambient n q m‖) := by
  exact Coeff.summable_norm_positive_weighted_of_squared_gap_tail
    (sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi q)) n
    (fun m => (2*Real.pi:ℂ)⁻¹*P.centeredMoment D.ambient n m 1 q)
    D.threshold D.constant D.constant_pos.le (fun m hm hmn => D.tail_bound q hq n m hm hmn)

theorem analytic_normalizedWeightedSecondMoment (P : HillProductEquationPatch)
    (D : MomentSeriesNeighborhood P) (n m : ℕ+) :
    AnalyticOnNhd ℂ (fun q => P.normalizedWeightedSecondMoment D.ambient n q m) D.source := by
  intro q hq
  exact analyticAt_const.mul (analyticAt_const.mul (P.analytic_centeredMoment D.cauchy n m 1 q (D.subset hq)))

theorem centeredSecondMomentSeries_eq_row_sum (P : HillProductEquationPatch)
    (D : MomentSeriesNeighborhood P) (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ D.source) :
    P.centeredSecondMomentSeries D.ambient n q =
      (2*Real.pi:ℂ)*(∑' k : ℤ, P.centeredSecondMomentRow D.ambient n q k) := by
  rw [centeredSecondMomentRow,Coeff.tsum_positiveSummableRealization _
    (P.summable_normalizedWeightedSecondMoment D n q hq),centeredSecondMomentSeries,← tsum_mul_left]
  apply tsum_congr
  intro m
  dsimp only [normalizedWeightedSecondMoment]
  have hpi : (Real.pi:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

end NLS.KdV.HillProductEquationPatch
