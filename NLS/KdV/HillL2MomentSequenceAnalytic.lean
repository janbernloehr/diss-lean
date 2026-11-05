import NLS.KdV.HillL2MomentSeriesBound
import NLS.KdV.HillMomentWeightedSeriesAnalytic
import NLS.SequenceSpaces.InfinityAnalyticRealization

/-! The ENTIRE original second-moment sequence is complex analytic in
the UNWEIGHTED infinity norm near every real L2 source. -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.LpSequence
open scoped ENNReal
namespace NLS.KdV.HillProductEquationPatch

def l2CenteredSecondMomentSequence (P : HillProductEquationPatch)
    (D : P.MomentSeriesNeighborhood) (q : Coeff 2) : Coeff ⊤ :=
  Coeff.ofFunctionOrZero ⊤ (positiveScalarExtension
    (fun n => P.centeredSecondMomentSeries D.ambient n (periodOneL2Inclusion q)))

theorem exists_local_l2CenteredSecondMomentSequence_analytic (P : HillProductEquationPatch)
    (D : P.MomentSeriesNeighborhood)
    (hfull : ∀ a ∈ D.source, ∀ n m : ℕ+,
      ‖(2*Real.pi:ℂ)⁻¹*P.centeredMoment D.ambient n m 1 a‖ ≤
        D.constant*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (P.sourcePsi a) (m:ℤ)‖^2*
          (if m=n then 1 else 1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ)))
    (q : Coeff 2) (hq : periodOneL2Inclusion q ∈ D.source)
    (hr : IsRealPeriodOneHminusOne (periodOneL2Inclusion q)) :
    ∃ U : Set (Coeff 2), IsOpen U ∧ q ∈ U ∧ (∀ r ∈ U, periodOneL2Inclusion r ∈ D.source) ∧
      AnalyticOnNhd ℂ (P.l2CenteredSecondMomentSequence D) U ∧
      ∃ R : ℝ, 0 ≤ R ∧ ∀ r ∈ U,
        ‖P.l2CenteredSecondMomentSequence D r‖ ≤ R ∧
        ∀ k, P.l2CenteredSecondMomentSequence D r k =
          positiveScalarExtension (fun n => P.centeredSecondMomentSeries D.ambient n (periodOneL2Inclusion r)) k := by
  obtain ⟨U,hU,hqU,hUD,R,hR,hbound⟩ := P.exists_local_l2CenteredSecondMomentSeries_bound D hfull q hq hr
  have ha (k : ℤ) : AnalyticOnNhd ℂ (fun r : Coeff 2 => positiveScalarExtension
      (fun n => P.centeredSecondMomentSeries D.ambient n (periodOneL2Inclusion r)) k) U := by
    intro r hrU
    exact (P.analytic_positive_centeredSecondMomentSeries D k _ (hUD r hrU)).comp
      (periodOneL2Inclusion.analyticAt r)
  have hb (r : Coeff 2) (hrU : r ∈ U) (k : ℤ) :
      ‖positiveScalarExtension (fun n => P.centeredSecondMomentSeries D.ambient n (periodOneL2Inclusion r)) k‖ ≤ R := by
    by_cases hk : k ∈ range positiveEmbedding
    · obtain ⟨n,rfl⟩ := hk
      change ‖positiveScalarExtension _ ((n:ℕ):ℤ)‖ ≤ R
      rw [positiveScalarExtension_apply]
      exact hbound r hrU n
    · rw [positiveScalarExtension_zero_of_not_mem_range _ k hk,norm_zero]
      exact hR
  obtain ⟨hA,hdata⟩ := Coeff.analytic_infty_realization_of_bound _ hU ha R hR hb
  exact ⟨U,hU,hqU,hUD,hA,R,hR,hdata⟩

end NLS.KdV.HillProductEquationPatch
