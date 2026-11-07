import NLS.KdV.HillHminusNativeSourceFactors
import NLS.ZakharovShabat.SourceRetainedEtaRemainderAnalytic
import NLS.ZakharovShabat.SourceBirkhoffOriginalMap

/-! The SAME actual own-index eta remainder has common scalar
analyticity on an original rough source neighborhood, including closed gaps. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV.HillHminusPsiChart

def sourceOwnEtaRemainder (P : HillHminusPsiChart) (n : ℤ) (q : PeriodOneHminusOne) : ℂ :=
  sourceAngularEtaRemainder (by norm_num) (by norm_num) n P.family.roots (P.dirichletSource q)

theorem exists_local_sourceOwnEtaRemainder_analytic (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num) P.family.originalDomain P.family.domain P.family.roots)
    (q : PeriodOneHminusOne) (hq : q∈P.sourceBetaDomain)
    (hr : periodOneL2Conjugation (P.miura.lift q)=P.miura.lift q) :
    ∃ U : Set PeriodOneHminusOne,IsOpen U ∧ q∈U ∧ U⊆P.sourceBetaDomain ∧
      ∀ n : ℤ,AnalyticOnNhd ℂ (P.sourceOwnEtaRemainder n) U := by
  obtain ⟨_B,D,_hactions⟩ := H.exists_original_birkhoff_map
  let φ : realTypeSourceSubmodule 2 := ⟨P.dirichletSource q,
    isRealType_sourcePhase _ (isRealType_hillMiuraDiagonal ⟨_,(periodOneL2Conjugation_fixed_iff _).mp hr⟩)⟩
  obtain ⟨V,hV,hφV,_hVW,ha⟩ := D.exists_local_ownEtaRemainder_common_analytic φ
  let U := P.sourceBetaDomain∩P.dirichletSource ⁻¹' V
  have hc : ContinuousOn P.dirichletSource P.sourceBetaDomain := P.analyticOnNhd_dirichletSource.continuousOn.mono inter_subset_left
  refine ⟨U,hc.isOpen_inter_preimage P.sourceBetaDomain_open hV,⟨hq,hφV⟩,inter_subset_left,?_⟩
  intro n a haU
  exact (ha n (P.dirichletSource a) haU.2).comp
    (f := P.dirichletSource) (P.analyticOnNhd_dirichletSource a haU.1.1)

end NLS.KdV.HillHminusPsiChart
