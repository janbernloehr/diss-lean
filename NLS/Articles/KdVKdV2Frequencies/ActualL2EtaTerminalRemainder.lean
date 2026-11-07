import NLS.Articles.KdVKdV2Frequencies.ActualL2FreeEtaRemainder
import NLS.Articles.KdVKdV2Frequencies.ActualL2OwnEtaPhaseData
import NLS.KdV.HillHminusEtaTerminal
import NLS.SequenceSpaces.AnalyticPhasePacketRemainder

/-! Remove the SAME eta's own-index remainder phase as well. The exact
free-amplitude core is now the literal Dirichlet/midpoint and terminal
sine data, with a TOTAL analytic one-derivative packet remainder. -/
noncomputable section
open Set Metric Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
variable {q0 : PeriodOneHminusOne}

theorem exists_l2_eta_terminal_remainder (D : RoughAbelianFourierDataAt q0)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion 1 (by norm_num) q))
    (hq : periodOneSobolevImageInclusion 1 (by norm_num) q∈ball q0 D.radius) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2),IsOpen U ∧ q∈U ∧
      ∃ CA CR : ℝ,∃ A : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → WeightedCoeff (Weight.sobolev 1) 2,
      ∃ R : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → WeightedCoeff (Weight.sobolev 2) 2,
        0≤CA ∧ 0≤CR ∧ AnalyticOnNhd ℂ A U ∧ AnalyticOnNhd ℂ R U ∧ ∀ p∈U,
          periodOneSobolevImageInclusion 1 (by norm_num) p∈ball q0 D.radius ∧ ‖A p‖≤CA ∧ ‖R p‖≤CR ∧
          (∀ j : ℤ,(R p).val j=D.packet (periodOneSobolevImageInclusion 1 (by norm_num) p) j-(A p).val j) ∧
          (∀ j : ℤ,j≤0 → (A p).val j=0) ∧ ∀ n : ℕ+,(A p).val (n:ℤ)=
            (Real.pi:ℂ)*(hillL2FreeAmplitude n:ℂ)*D.chart.sourceEtaTerminal (n:ℤ)
              (periodOneSobolevImageInclusion 1 (by norm_num) p) := by
  let L := periodOneSobolevImageInclusion 1 (by norm_num : (0:ℝ)≤1)
  obtain ⟨V,hV,hqV,CA0,CR0,A0,R0,hCA0,hCR0,hA0a,hR0a,h0⟩ := D.exists_l2_free_eta_remainder q hr hq
  obtain ⟨W,hW,hqW,CN,CM,N,M,hCN,hCM,hNa,hMa,hphase⟩ := D.exists_l2_own_eta_phase_data q hr hq
  obtain ⟨U,hU,hqU,hUV,hUW,A,R,hAa,hRa,hd⟩ := Coeff.exists_analytic_phase_packet_remainder V W hV hW q hqV hqW
    (fun p => D.packet (L p)) A0 R0 N M (fun n p => exp (I*D.chart.sourceOwnEtaRemainder (n:ℤ) (L p)))
    CA0 CR0 CN CM hCN hCM hA0a hR0a hNa hMa
    (fun p hp => (h0 p hp).2.1) (fun p hp => (h0 p hp).2.2.1)
    (fun p hp => (hphase p hp).1) (fun p hp => (hphase p hp).2.1)
    (fun p hp => (h0 p hp).2.2.2.1) (fun p hp => (h0 p hp).2.2.2.2.1)
    (fun p hp n => ((hphase p hp).2.2 n).2.1) (fun p hp n => ((hphase p hp).2.2 n).2.2)
  refine ⟨U,hU,hqU,CN*CA0,CR0+CM*(CN*CA0),A,R,by positivity,by positivity,hAa,hRa,?_⟩
  intro p hp
  refine ⟨(h0 p (hUV hp)).1,(hd p hp).1,(hd p hp).2.1,(hd p hp).2.2.1,(hd p hp).2.2.2.1,?_⟩
  intro n
  have hN := ((hphase p (hUW hp)).2.2 n).1
  rw [(hd p hp).2.2.2.2 n,hN,(h0 p (hUV hp)).2.2.2.2.2 n]
  calc
    _ = (Real.pi:ℂ)*(hillL2FreeAmplitude n:ℂ)*(D.chart.sourceEtaSequence (L p) (n:ℤ)*
        exp (-I*D.chart.sourceOwnEtaRemainder (n:ℤ) (L p))) := by ring
    _ = _ := by rw [D.chart.sourceEtaSequence_unphase D.roots (L p) (D.source_domain (h0 p (hUV hp)).1) (n:ℤ)]

end NLS.Articles.KdVKdV2Frequencies.RoughAbelianFourierDataAt
