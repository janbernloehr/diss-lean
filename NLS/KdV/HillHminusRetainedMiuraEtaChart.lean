import NLS.KdV.HillHminusAllSobolevEtaCharts
import NLS.KdV.HillHminusSobolevEtaCompactDerivative

/-! # Actual eta charts retaining their SAME native Miura lift witnesses -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

/-- All native complex Sobolev germs of the SAME supplied actual lift. -/
def HasAllNativeMiuraGerms (P : HillHminusPsiChart) : Prop :=
  ∀ t : ℝ, ∀ ht : 0≤t, ∀ q : WeightedCoeff (Weight.sobolev (t-1)) 2,
    periodOneSobolevImageInclusion t ht q∈P.miura.domain →
    ∃ V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2), IsOpen V ∧ q∈V ∧
      ∃ g : WeightedCoeff (Weight.sobolev (t-1)) 2 → WeightedCoeff (Weight.sobolev t) 2,
        AnalyticOnNhd ℂ g V ∧ ∀ p∈V,
          periodOneSobolevImageInclusion t ht p∈P.miura.domain ∧
          WeightedCoeff.sobolevToL2 ht (g p)=P.miura.lift (periodOneSobolevImageInclusion t ht p)

/-- At EVERY real rough base, ONE actual chart and original root witness
retain ALL native Miura lift germs, real form and original endpoint labels. -/
theorem exists_hillHminus_retained_Miura_eta_chart
    (q0 : PeriodOneHminusOne) (hr0 : IsRealPeriodOneHminusOne q0) :
    ∃ P : HillHminusPsiChart, ∃ c : ℝ,
      0<c ∧ P.miura.energyShift=(c : ℂ)^2 ∧ q0∈P.sourceBetaDomain ∧
      (∀ q∈P.miura.domain, IsRealPeriodOneHminusOne q →
        periodOneL2Conjugation (P.miura.lift q)=P.miura.lift q) ∧
      (∀ q∈P.miura.domain, hillHminusRadicand q (-P.miura.energyShift)≠0) ∧
      (∀ q∈P.miura.domain, ∀ hr : IsRealPeriodOneHminusOne q, ∀ n : ℕ, 0<n →
        hillHminusRealLabels q hr (2*n-1)=(hillMiuraDiracLeft (P.miura.lift q) n).re^2-c^2 ∧
        hillHminusRealLabels q hr (2*n)=(hillMiuraDiracRight (P.miura.lift q) n).re^2-c^2) ∧
      ∃ _H : SourceLemma12_12Data (by norm_num) (by norm_num)
        P.family.originalDomain P.family.domain P.family.roots, HasAllNativeMiuraGerms P := by
  obtain ⟨C,c,hc,hshift,hqC,hreal,houtside,hlabels,hstrong⟩ :=
    exists_hillHminus_real_Miura_all_strong_sobolev_chart q0 hr0
  obtain ⟨A,H⟩ := exists_miuraHillPsiFamily_with_original_estimates
  let P : HillHminusPsiChart := ⟨C,A⟩
  have hu := (periodOneL2Conjugation_fixed_iff _).mp (hreal q0 hqC hr0)
  have hsource : q0∈P.source := ⟨hqC,A.real_mem_source ⟨C.lift q0,hu⟩⟩
  exact ⟨P,c,hc,hshift,P.mem_sourceBetaDomain_of_real q0 hsource hu,hreal,houtside,hlabels,H,hstrong⟩

/-- Retained actual Miura germs give the Fourier principal for ANY given
native eta realization at EVERY eligible real base and ALL native orders. -/
theorem HillHminusPsiChart.isCompactOperator_native_eta_sub_fourier_of_retained
    (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (hstrong : HasAllNativeMiuraGerms P)
    (t : ℝ) (ht : 0≤t)
    (V : Set (WeightedCoeff (Weight.sobolev (t-1)) 2)) (hV : IsOpen V)
    (F : WeightedCoeff (Weight.sobolev (t-1)) 2 → Coeff 2)
    (hF : ∀ p∈V, periodOneSobolevImageInclusion t ht p∈P.sourceBetaDomain ∧
      ∀ n : ℤ, F p n=(Weight.sobolev t n : ℂ)*P.sourceEtaSequence (periodOneSobolevImageInclusion t ht p) n)
    (q : WeightedCoeff (Weight.sobolev (t-1)) 2) (hq : q∈V)
    (hr : periodOneL2Conjugation (P.miura.lift (periodOneSobolevImageInclusion t ht q))=
      P.miura.lift (periodOneSobolevImageInclusion t ht q)) :
    IsCompactOperator (fderiv ℂ F q-
      ((Coeff.holderProduct (q := 2)
        (sourceEtaNormalizationSymbol (by norm_num) (by norm_num) P.family.roots 1
          (P.dirichletSource (periodOneSobolevImageInclusion t ht q)))).comp
        ((2*I) • (WeightedCoeff.weightIsometry (Weight.sobolev t) 2).toContinuousLinearEquiv.toContinuousLinearMap)).comp
          (periodOneSobolevFreeMassEquiv 0 t ht).symm.toContinuousLinearMap) := by
  obtain ⟨U,hU,hqU,g,hga,hg⟩ := hstrong t ht q (hF q hq).1.1.1
  exact P.isCompactOperator_native_eta_derivative_sub_principal H t ht U hU g hga hg V hV F hF q hqU hq hr

end NLS.KdV
