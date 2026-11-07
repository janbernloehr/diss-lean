import NLS.Articles.KdVKdV2Frequencies.ActualL2EtaTerminalRemainder
import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianNativeGerms

/-! The SAME global physical forward map has its actual literal eta
terminal core plus a TOTAL analytic one-derivative remainder. Both source
conjugation and EVERY stored physical output sign are retained. -/
noncomputable section
open Set Metric Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem exists_actual_l2_eta_terminal_decomposition (D : GlobalRoughAbelianForwardData)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hqr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion 1 (by norm_num) q)) :
    let q0 : PeriodOneRealHminusOne := ⟨periodOneSobolevImageInclusion 1 (by norm_num) q,hqr⟩
    let E := D.chart q0
    ∃ U : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2), IsOpen U ∧ q∈U ∧
      ∃ CA CR : ℝ, ∃ A : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → WeightedCoeff (Weight.sobolev 1) 2,
      ∃ R : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → WeightedCoeff (Weight.sobolev 2) 2,
        0≤CA ∧ 0≤CR ∧ AnalyticOnNhd ℂ A U ∧ AnalyticOnNhd ℂ R U ∧ ∀ p∈U,
          periodOneSobolevImageInclusion 1 (by norm_num) p∈D.domain ∧ ‖A p‖≤CA ∧ ‖R p‖≤CR ∧
          (∀ j : ℤ, D.positive (periodOneSobolevImageInclusion 1 (by norm_num) p) j=
            if E.signs j then -((A p).val j+(R p).val j) else (A p).val j+(R p).val j) ∧
          (∀ j : ℤ, j≤0 → (A p).val j=0) ∧
          ∀ n : ℕ+, (A p).val (n:ℤ)=(Real.pi:ℂ)*(hillL2FreeAmplitude n:ℂ)*
            E.data.chart.sourceEtaTerminal (n:ℤ) (periodOneSobolevImageInclusion 1 (by norm_num) p) := by
  let q0 : PeriodOneRealHminusOne := ⟨periodOneSobolevImageInclusion 1 (by norm_num) q,hqr⟩
  let E := D.chart q0
  obtain ⟨U,hU,hqU,CA,CR,A,R,hCA,hCR,hAa,hRa,hdata⟩ :=
    E.data.exists_l2_eta_terminal_remainder q hqr (mem_ball_self E.data.radius_pos)
  refine ⟨U,hU,hqU,CA,CR,A,R,hCA,hCR,hAa,hRa,?_⟩
  intro p hp
  have hd := hdata p hp
  refine ⟨D.chart_subset_domain q0 hd.1,hd.2.1,hd.2.2.1,?_,hd.2.2.2.2⟩
  intro j
  have he : E.data.packet (periodOneSobolevImageInclusion 1 (by norm_num) p) j=
      (A p).val j+(R p).val j := by
    have h := hd.2.2.2.1 j
    exact ((sub_eq_iff_eq_add).mp h.symm).trans (add_comm _ _)
  rw [D.positive_local q0 hd.1]
  change Coeff.signChange E.signs (E.data.packet (periodOneSobolevImageInclusion 1 (by norm_num) p)) j=_
  rw [Coeff.signChange_apply,he]

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
