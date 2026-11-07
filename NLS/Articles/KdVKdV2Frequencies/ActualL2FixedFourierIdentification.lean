import NLS.Articles.KdVKdV2Frequencies.ActualL2FourierSignTail
import NLS.SequenceSpaces.AnalyticFiniteSignCorrection
import NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianNativeGerms

/-! ONE fixed physical Fourier orientation, chosen at zero BEFORE every
source, gives the SAME actual forward map with TOTAL analytic h2 remainder. -/
noncomputable section
open Set Metric Complex Filter NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

theorem exists_actual_l2_fixed_fourier_decomposition (D : GlobalRoughAbelianForwardData)
    (q : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2)
    (hqr : IsRealPeriodOneHminusOne (periodOneSobolevImageInclusion 1 (by norm_num) q)) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2), IsOpen U ∧ q∈U ∧
      ∃ CA CR : ℝ, ∃ A : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → WeightedCoeff (Weight.sobolev 1) 2,
      ∃ R : WeightedCoeff (Weight.sobolev ((1:ℝ)-1)) 2 → WeightedCoeff (Weight.sobolev 2) 2,
        0≤CA ∧ 0≤CR ∧ AnalyticOnNhd ℂ A U ∧ AnalyticOnNhd ℂ R U ∧ ∀ p∈U,
          periodOneSobolevImageInclusion 1 (by norm_num) p∈D.domain ∧ ‖A p‖≤CA ∧ ‖R p‖≤CR ∧
          (∀ j : ℤ, D.positive (periodOneSobolevImageInclusion 1 (by norm_num) p) j=
            if D.fixedFourierSigns j then -((A p).val j+(R p).val j) else (A p).val j+(R p).val j) ∧
          (∀ j : ℤ, j≤0 → (A p).val j=0) ∧
          ∀ n : ℕ+, (A p).val (n:ℤ)=(hillL2FreeAmplitude n:ℂ)/(1+(n:ℂ))*p.val (n:ℤ) := by
  let q0 : PeriodOneRealHminusOne := ⟨periodOneSobolevImageInclusion 1 (by norm_num) q,hqr⟩
  let E := D.chart q0
  obtain ⟨U,hU,hqU,CA,CR,A,R,hCA,hCR,hAa,hRa,hd⟩ := D.exists_actual_l2_original_fourier_decomposition q hqr
  obtain ⟨N,hN⟩ := eventually_atTop.mp (D.eventually_eq_fixed_fourier_signs q hqr)
  obtain ⟨CS,S,hCS,hSa,hs⟩ := WeightedCoeff.exists_analytic_finite_sign_correction U E.signs D.fixedFourierSigns N hN
    A R (fun p j => D.positive (periodOneSobolevImageInclusion 1 (by norm_num) p) j) CA CR hCA hCR hAa hRa
    (fun p hp => (hd p hp).2.1) (fun p hp => (hd p hp).2.2.1)
    (fun p hp => (hd p hp).2.2.2.2.1) (fun p hp => (hd p hp).2.2.2.1)
  refine ⟨U,hU,hqU,CA,CS,A,S,hCA,hCS,hAa,hSa,?_⟩
  intro p hp
  exact ⟨(hd p hp).1,(hd p hp).2.1,(hs p hp).1,(hs p hp).2,(hd p hp).2.2.2.2⟩

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
