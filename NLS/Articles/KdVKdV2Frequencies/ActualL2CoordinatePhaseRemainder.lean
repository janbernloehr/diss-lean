import NLS.Articles.KdVKdV2Frequencies.ActualL2CoordinatePhaseData

/-! The noncentral phase in the ACTUAL Abelian coordinate formula contributes
an analytic one-derivative remainder near EVERY eligible real L2 source.
Amplitude and spectral Fourier remainders remain separate obligations. -/
noncomputable section
open Set Metric Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
variable {q0 : PeriodOneHminusOne}

theorem exists_l2_coordinate_phase_remainder
    (D : RoughAbelianFourierDataAt q0)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hqr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion 1 (by norm_num) q))
    (hq : periodOneSobolevImageInclusion 1 (by norm_num) q∈ball q0 D.radius) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2), IsOpen U ∧ q∈U ∧
      ∃ CA CR : ℝ, ∃ A : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → WeightedCoeff (Weight.sobolev 1) 2,
      ∃ R : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → WeightedCoeff (Weight.sobolev 2) 2,
        0≤CA ∧ 0≤CR ∧ AnalyticOnNhd ℂ A U ∧ AnalyticOnNhd ℂ R U ∧ ∀ p∈U,
          periodOneSobolevImageInclusion 1 (by norm_num) p∈ball q0 D.radius ∧ ‖A p‖≤CA ∧ ‖R p‖≤CR ∧
          (∀ j : ℤ, (R p).val j=D.packet (periodOneSobolevImageInclusion 1 (by norm_num) p) j-(A p).val j) ∧
          ∀ n : ℕ+, (A p).val (n:ℤ)=D.amplitude (periodOneSobolevImageInclusion 1 (by norm_num) p) (n:ℤ)*
            D.chart.sourceNormalizedMidpoint n (periodOneSobolevImageInclusion 1 (by norm_num) p)*
              D.chart.sourceEtaSequence (periodOneSobolevImageInclusion 1 (by norm_num) p) (n:ℤ) := by
  obtain ⟨U,hU,hqU,B,C,K,F,N,M,hB,hC,hK,hFa,hNa,hMa,hdata⟩ :=
    D.exists_l2_coordinate_phase_data q hqr hq
  let L := periodOneSobolevImageInclusion 1 (by norm_num : (0:ℝ)≤1)
  obtain ⟨A,R,hAa,hRa,hd⟩ := Coeff.exists_analytic_weighted_phase_remainder U
    (fun p => D.packet (L p)) F N M B C K hC hK hFa hNa hMa
    (fun p hp => (hdata p hp).2.1) (fun p hp => (hdata p hp).2.2.1)
    (fun p hp => (hdata p hp).2.2.2.1) (fun p hp => (hdata p hp).2.2.2.2.1)
    (fun p hp => (hdata p hp).2.2.2.2.2.1)
  refine ⟨U,hU,hqU,C*B,K*(C*B),A,R,by positivity,by positivity,hAa,hRa,?_⟩
  intro p hp
  obtain ⟨hpD,_hFb,_hNb,_hMb,_hFc,_hc,hInv⟩ := hdata p hp
  refine ⟨hpD,(hd p hp).1,(hd p hp).2.1,(hd p hp).2.2.2,?_⟩
  intro n
  rw [(hd p hp).2.2.1 (n:ℤ),D.packet_coordinates _ hpD n,hInv n]
  have he : exp (I*D.chart.sourceNoncentralBeta n (L p))*exp (-I*D.chart.sourceNoncentralBeta n (L p))=1 := by
    rw [←exp_add,show I*D.chart.sourceNoncentralBeta n (L p)+-I*D.chart.sourceNoncentralBeta n (L p)=0 by ring,exp_zero]
  unfold HillHminusPsiChart.sourceAbelianCoordinateFormula
  calc
    _ = (D.amplitude (L p) (n:ℤ)*D.chart.sourceNormalizedMidpoint n (L p)*D.chart.sourceEtaSequence (L p) (n:ℤ))*
        (exp (I*D.chart.sourceNoncentralBeta n (L p))*exp (-I*D.chart.sourceNoncentralBeta n (L p))) := by ring
    _ = _ := by rw [he,mul_one]

end NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
