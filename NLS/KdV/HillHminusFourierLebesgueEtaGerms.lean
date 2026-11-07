import NLS.ComplexAnalysis.AnalyticGermPullback
import NLS.KdV.HillMiuraFourierLebesgueEtaGerms
import NLS.KdV.HillHminusRetainedFourierLebesgueMiuraGerms

/-! # Strong analytic eta germs of the SAME retained rough Hill chart

The supplied Hilbert root family is recovered on the entire real slice,
with a bounded complex analytic germ in the native Fourier-Lebesgue norm.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusPsiChart

theorem exists_native_fourierLebesgue_eta_germ (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (hstrong : HasAllNativeMiuraGerms P)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a →
      periodOneL2Conjugation (P.miura.lift a)=P.miura.lift a)
    (s p : ℝ) (hs : -1/2≤s) (hp : 2<p) [Fact (1≤ENNReal.ofReal p)]
    (q : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p))
    (hq : periodOneFourierLebesgueImageInclusion s p hs hp q∈P.sourceBetaDomain)
    (hqr : IsRealPeriodOneHminusOne (periodOneFourierLebesgueImageInclusion s p hs hp q)) :
    ∃ V : Set (WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p)), IsOpen V ∧ q∈V ∧
      ∃ M : ℝ, ∃ E : WeightedCoeff (Weight.sobolev s) (ENNReal.ofReal p) → Coeff (ENNReal.ofReal p),
        0≤M ∧ AnalyticOnNhd ℂ E V ∧ ∀ a∈V,
          periodOneFourierLebesgueImageInclusion s p hs hp a∈P.sourceBetaDomain ∧ ‖E a‖≤M ∧
          (IsRealPeriodOneHminusOne (periodOneFourierLebesgueImageInclusion s p hs hp a) →
            ∀ n : ℤ, E a n=(Weight.sobolev (s+1) n : ℂ)*
              P.sourceEtaSequence (periodOneFourierLebesgueImageInclusion s p hs hp a) n) := by
  let L := periodOneFourierLebesgueImageInclusion s p hs hp
  obtain ⟨U,hU,hqU,g,hga,hg⟩ := P.exists_fourierLebesgue_native_Miura_lift hstrong s p hs hp q hq.1.1
  have h2p : (2 : ℝ≥0∞)≤ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hp.le
  have ht : 0≤s+1 := by linarith
  obtain ⟨A,hA,hgqA,M,F,hM,hFa,hF⟩ := exists_hillMiuraFourierLebesgueEta_germ H
    ENNReal.ofReal_ne_top h2p (s+1) ht (g q) (P.miura.lift (L q))
      ((hg q hqU).2) (hreal _ hq.1.1 hqr)
  obtain ⟨V,hV,hqV,E,hEa,hE⟩ := NLS.ComplexAnalysis.analytic_germ_pullback_properties
    L P.sourceBetaDomain P.sourceBetaDomain_open q hq U hU hqU g hga A hA hgqA F hFa
    (fun a e => L a∈P.sourceBetaDomain ∧ ‖e‖≤M ∧
      (IsRealPeriodOneHminusOne (L a) → ∀ n : ℤ,
        e n=(Weight.sobolev (s+1) n : ℂ)*P.sourceEtaSequence (L a) n)) (by
      intro a ha haA haD
      refine ⟨haD,(hF (g a) haA).1,?_⟩
      intro har n
      have he := (hF (g a) haA).2 (P.miura.lift (L a)) ((hg a ha).2)
        (hreal _ (hg a ha).1 har) n
      rw [P.sourceEtaSequence_apply H (L a) haD n]
      exact he)
  exact ⟨V,hV,hqV,M,E,hM,hEa,hE⟩

end NLS.KdV.HillHminusPsiChart
