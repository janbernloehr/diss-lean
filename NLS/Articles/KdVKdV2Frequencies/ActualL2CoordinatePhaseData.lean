import NLS.Articles.KdVKdV2Frequencies.ArbitraryBaseAbelianFourierGerms
import NLS.KdV.HillHminusL2CoordinatePhaseSmoothing
import NLS.SequenceSpaces.AnalyticWeightedPhaseRemainder

/-! Common analytic normalization data for the ACTUAL coordinate phase,
with one complex L2 neighborhood before every label. -/
noncomputable section
open Set Metric Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
variable {q0 : PeriodOneHminusOne}

theorem exists_l2_coordinate_phase_data
    (D : RoughAbelianFourierDataAt q0)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hqr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion 1 (by norm_num) q))
    (hq : periodOneSobolevImageInclusion 1 (by norm_num) q∈ball q0 D.radius) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2), IsOpen U ∧ q∈U ∧
      ∃ B C K : ℝ, ∃ F : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → Coeff 2,
      ∃ N M : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → Coeff ⊤,
        0≤B ∧ 0≤C ∧ 0≤K ∧ AnalyticOnNhd ℂ F U ∧ AnalyticOnNhd ℂ N U ∧ AnalyticOnNhd ℂ M U ∧
        ∀ p∈U, periodOneSobolevImageInclusion 1 (by norm_num) p∈ball q0 D.radius ∧
          ‖F p‖≤B ∧ ‖N p‖≤C ∧ ‖M p‖≤K ∧
          (∀ j : ℤ, F p j=(Weight.sobolev 1 j:ℂ)*D.packet (periodOneSobolevImageInclusion 1 (by norm_num) p) j) ∧
          (∀ j : ℤ, M p j*N p j*D.packet (periodOneSobolevImageInclusion 1 (by norm_num) p) j=
            (Weight.sobolev 1 j:ℂ)*(D.packet (periodOneSobolevImageInclusion 1 (by norm_num) p) j-
              N p j*D.packet (periodOneSobolevImageInclusion 1 (by norm_num) p) j)) ∧
          ∀ n : ℕ+, N p (n:ℤ)=exp (-I*D.chart.sourceNoncentralBeta n
            (periodOneSobolevImageInclusion 1 (by norm_num) p)) := by
  let L := periodOneSobolevImageInclusion 1 (by norm_num : (0:ℝ)≤1)
  obtain ⟨V,hV,hqV,B,F,hB,hFa,hF⟩ := D.exists_native_packet_fourier_germ 1 (by norm_num) q hqr hq
  obtain ⟨W,hW,hqW,_hWP,K,M,hK,hMa,hM⟩ := D.chart.exists_native_l2_coordinate_phase_smoothing
    D.roots D.native_lifts q (D.source_domain hq) (D.real_lift _ (D.source_domain hq).1.1 hqr)
  obtain ⟨Z,hZ,hqZ,_hZP,C,_σ,N,hC,_hσa,hNa,hN⟩ :=
    D.chart.exists_local_native_sourceNoncentralPhase_reciprocal D.roots (L q) (D.source_domain hq)
  have hNid (a : PeriodOneHminusOne) (ha : a∈Z) (n : ℕ+) :
      exp (I*D.chart.sourceNoncentralBeta n a)*N a (n:ℤ)=1 := by
    have h := ((hN a ha).2.2.2 n).2.2.2
    rw [((hN a ha).2.2.2 n).1] at h
    exact h
  obtain ⟨U,hU,hqU,hFaU,hNaU,hMaU,hdata⟩ := Coeff.exists_common_analytic_phase_packet_data
    L V W Z q hV hW hZ hqV hqW hqZ D.packet F N M
    (fun n a => exp (I*D.chart.sourceNoncentralBeta n a))
    (fun n a => exp (-I*D.chart.sourceNoncentralBeta n a)) (fun a => a∈ball q0 D.radius)
    B C K hFa hNa hMa (fun p hp => (hF p hp).2.1) (fun a ha => (hN a ha).2.1)
    (fun p hp => (hM p hp).1) (fun p hp => (hF p hp).2.2.1)
    (fun p hp j hj => (D.packet_data (L p) (hF p hp).1).2.2 j hj)
    (fun p hp n => (hM p hp).2.2.1 n) hNid
    (fun a ha n => ((hN a ha).2.2.2 n).2.1) (fun p hp => (hF p hp).1)
  exact ⟨U,hU,hqU,B,C,K,F,(fun p => N (L p)),M,hB,hC.le,hK,hFaU,hNaU,hMaU,hdata⟩

end NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
