import NLS.Articles.KdVKdV2Frequencies.ArbitraryBaseAbelianFourierData
import NLS.KdV.HillHminusL2OwnEtaDecay
import NLS.SequenceSpaces.AnalyticPositivePhaseData

/-! Actual own-index eta inverse phase and weighted exponential error
on ONE original complex L2 neighborhood, before all positive labels. -/
noncomputable section
open Set Metric Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
variable {q0 : PeriodOneHminusOne}

theorem exists_l2_own_eta_phase_data (D : RoughAbelianFourierDataAt q0)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion 1 (by norm_num) q))
    (hq : periodOneSobolevImageInclusion 1 (by norm_num) q∈ball q0 D.radius) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2),IsOpen U ∧ q∈U ∧
      ∃ CN CM : ℝ,∃ N M : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → Coeff ⊤,
        0≤CN ∧ 0≤CM ∧ AnalyticOnNhd ℂ N U ∧ AnalyticOnNhd ℂ M U ∧ ∀ p∈U,
          ‖N p‖≤CN ∧ ‖M p‖≤CM ∧ ∀ n : ℕ+,
            N p (n:ℤ)=exp (-I*D.chart.sourceOwnEtaRemainder (n:ℤ) (periodOneSobolevImageInclusion 1 (by norm_num) p)) ∧
            M p (n:ℤ)=(1+(n:ℂ))*(exp (I*D.chart.sourceOwnEtaRemainder (n:ℤ) (periodOneSobolevImageInclusion 1 (by norm_num) p))-1) ∧
            exp (I*D.chart.sourceOwnEtaRemainder (n:ℤ) (periodOneSobolevImageInclusion 1 (by norm_num) p))*N p (n:ℤ)=1 := by
  let L := periodOneSobolevImageInclusion 1 (by norm_num : (0:ℝ)≤1)
  obtain ⟨U,hU,hqU,_hUP,hRa,K,hK,hb⟩ := D.chart.exists_native_l2_own_eta_decay D.roots D.native_lifts q
    (D.source_domain hq) (D.real_lift _ (D.source_domain hq).1.1 hr)
  have hbound (p) (hp : p∈U) (n : ℕ+) : (1+(n:ℝ))*‖D.chart.sourceOwnEtaRemainder (n:ℤ) (L p)‖≤K := by
    simpa only [Int.cast_natCast,abs_of_pos (by positivity : (0:ℝ)<n)] using hb p hp (n:ℤ)
  obtain ⟨N,M,hNa,hMa,hd⟩ := Coeff.exists_positive_analytic_phase_data U hU
    (fun n p => D.chart.sourceOwnEtaRemainder (n:ℤ) (L p)) (fun n => hRa (n:ℤ)) K hK hbound
  refine ⟨U,hU,hqU,Real.exp K,K*Real.exp K,N,M,(Real.exp_pos K).le,by positivity,hNa,hMa,?_⟩
  intro p hp
  exact ⟨(hd p hp).1,(hd p hp).2.1,(hd p hp).2.2.2⟩

end NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
