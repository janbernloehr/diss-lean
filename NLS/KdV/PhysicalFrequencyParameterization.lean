import NLS.KdV.PhysicalSobolevLpFrequencyChart
import NLS.ComplexAnalysis.CommonPullbackDomain

/-! Exact analytic parameterizations of an actual physical frequency
chart. The source Banach space and rough inclusion remain opaque. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ENNReal
namespace NLS.KdV

structure PhysicalFrequencyParameterization (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (t : ℝ) (ht : 0≤t) (J : E →L[ℂ] PeriodOneHminusOne) where
  physical : PhysicalMiuraFrequencyChart
  estimates : SourceLemma12_12Data (by norm_num) (by norm_num)
    physical.psi.family.originalDomain physical.psi.family.domain physical.psi.family.roots
  domain : Set E
  domain_open : IsOpen domain
  domain_subset : domain⊆J ⁻¹' physical.domain
  normalizedSource : E → CoeffPair 2
  analytic_source : AnalyticOnNhd ℂ normalizedSource domain
  real_source : ∀ a∈domain, IsRealPeriodOneHminusOne (J a) → normalizedSource a∈realTypeSourceLocus 2
  source_identity : ∀ a∈domain,
    normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht) (normalizedSource a)=
      hillMiuraDiagonal (physical.psi.miura.lift (J a))

theorem exists_physicalFrequencyParameterization_of_germ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (B : PhysicalMiuraFrequencyChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      B.psi.family.originalDomain B.psi.family.domain B.psi.family.roots)
    (t : ℝ) (ht : 0≤t) (J : E →L[ℂ] PeriodOneHminusOne)
    (V : Set E) (hV : IsOpen V) (η : E → CoeffPair 2) (hη : AnalyticOnNhd ℂ η V)
    (hrη : ∀ a∈V, IsRealPeriodOneHminusOne (J a) → η a∈realTypeSourceLocus 2)
    (he : ∀ a∈V, normalizedWeightedSourceCLM (p := 2) (sourceSobolevSpectralWeight t ht) (η a)=
      hillMiuraDiagonal (B.psi.miura.lift (J a)))
    (q : E) (hqV : q∈V) (hqB : J q∈B.domain) :
    ∃ A : PhysicalFrequencyParameterization E t ht J, q∈A.domain := by
  obtain ⟨T,hT,hqT,hTV,_hTS,hTB⟩ := exists_open_common_pullback_domain V hV q hqV
    η hη.continuousOn univ isOpen_univ (mem_univ _) J J.continuous B.domain B.domain_open hqB
  exact ⟨{
    physical := B
    estimates := H
    domain := T
    domain_open := hT
    domain_subset := hTB
    normalizedSource := η
    analytic_source := hη.mono hTV
    real_source := fun a ha => hrη a (hTV ha)
    source_identity := fun a ha => he a (hTV ha)
  },hqT⟩

end NLS.KdV
