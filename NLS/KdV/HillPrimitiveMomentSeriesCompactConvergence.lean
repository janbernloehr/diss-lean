import NLS.KdV.HillPrimitiveMomentSeriesAnalytic
import NLS.SequenceSpaces.LocallyUniformSummation

/-! Literal finite weighted moment sums converge uniformly on every
compact complex source set. No uniform-tail claim on a Banach ball
is needed for the separately proved Banach-source analyticity. -/
noncomputable section
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.LpSequence
open scoped ENNReal Classical
namespace NLS.KdV.HillProductEquationPatch

def centeredSecondMomentPartialSum (P : HillProductEquationPatch) (W : Set (CoeffPair 2))
    (n : ℕ+) (N : ℕ) (q : PeriodOneHminusOne) : ℂ :=
  ∑ k ∈ Finset.Icc (-(N:ℤ)) N,
    positiveScalarExtension (fun m : ℕ+ => ((m:ℕ):ℂ)*P.centeredMoment W n m 1 q) k

theorem two_pi_mul_centeredSecondMomentRow_apply (P : HillProductEquationPatch)
    (D : MomentSeriesNeighborhood P) (n : ℕ+) (q : PeriodOneHminusOne) (hq : q ∈ D.source) (k : ℤ) :
    (2*Real.pi:ℂ)*P.centeredSecondMomentRow D.ambient n q k=
      positiveScalarExtension (fun m : ℕ+ => ((m:ℕ):ℂ)*P.centeredMoment D.ambient n m 1 q) k := by
  rw [centeredSecondMomentRow,Coeff.positiveSummableRealization_apply _
    (P.summable_normalizedWeightedSecondMoment D n q hq)]
  by_cases hk : k ∈ range positiveEmbedding
  · obtain ⟨m,rfl⟩ := hk
    change (2*Real.pi:ℂ)*positiveScalarExtension (P.normalizedWeightedSecondMoment D.ambient n q) ((m:ℕ):ℤ)=
      positiveScalarExtension (fun j : ℕ+ => ((j:ℕ):ℂ)*P.centeredMoment D.ambient n j 1 q) ((m:ℕ):ℤ)
    rw [positiveScalarExtension_apply,positiveScalarExtension_apply]
    dsimp only [normalizedWeightedSecondMoment]
    have hpi : (Real.pi:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
  · rw [positiveScalarExtension_zero_of_not_mem_range _ k hk,
      positiveScalarExtension_zero_of_not_mem_range _ k hk,mul_zero]

theorem centeredSecondMomentPartialSum_eq_row_sum (P : HillProductEquationPatch)
    (D : MomentSeriesNeighborhood P) (n : ℕ+) (N : ℕ)
    (q : PeriodOneHminusOne) (hq : q ∈ D.source) :
    P.centeredSecondMomentPartialSum D.ambient n N q=
      (2*Real.pi:ℂ)*(∑ k ∈ Finset.Icc (-(N:ℤ)) N, P.centeredSecondMomentRow D.ambient n q k) := by
  rw [centeredSecondMomentPartialSum,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => (P.two_pi_mul_centeredSecondMomentRow_apply D n q hq k).symm)

theorem tendstoUniformlyOn_centeredSecondMomentPartialSum_of_isCompact (P : HillProductEquationPatch)
    (D : MomentSeriesNeighborhood P) (n : ℕ+) (K : Set PeriodOneHminusOne)
    (hK : IsCompact K) (hKD : K ⊆ D.source) :
    TendstoUniformlyOn (P.centeredSecondMomentPartialSum D.ambient n)
      (P.centeredSecondMomentSeries D.ambient n) atTop K := by
  have hc := Coeff.tendstoUniformlyOn_sums_of_isCompact
    (P.centeredSecondMomentRow D.ambient n) K hK
    ((P.analytic_centeredSecondMomentRow D n).continuousOn.mono hKD)
  let L : ℂ →L[ℂ] ℂ := (2*Real.pi:ℂ) • ContinuousLinearMap.id ℂ ℂ
  have hconv := L.uniformContinuous.comp_tendstoUniformlyOn hc
  change TendstoUniformlyOn
    (fun (N : ℕ) q => (2*Real.pi:ℂ)*(∑ k ∈ Finset.Icc (-(N:ℤ)) N, P.centeredSecondMomentRow D.ambient n q k))
    (fun q => (2*Real.pi:ℂ)*(∑' k : ℤ, P.centeredSecondMomentRow D.ambient n q k)) atTop K at hconv
  rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
  intro ε hε
  filter_upwards [hconv ε hε] with N hN q hq
  rw [P.centeredSecondMomentPartialSum_eq_row_sum D n N q (hKD hq),
    P.centeredSecondMomentSeries_eq_row_sum D n q (hKD hq)]
  exact hN q hq

end NLS.KdV.HillProductEquationPatch
