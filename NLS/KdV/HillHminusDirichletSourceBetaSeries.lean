import NLS.KdV.HillHminusPhaseNumeratorCompatibility
import NLS.ZakharovShabat.SourceAngularOriginalBetaSeries

/-! Actual ordinary-source correction series in the H-minus-one chart.
The source, signed labels, multipliers, sheets and normalized numerators
have been compared exactly. Identifying the scalar physical phase path
integrals with the appropriate source integrals remains a separate step. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart

/-- The SAME verified psi family is evaluated at the actual ordinary
Dirichlet source on this common complex H-minus-one domain. -/
def sourceBetaDomain (P : HillHminusPsiChart) : Set PeriodOneHminusOne :=
  P.source∩P.dirichletSource ⁻¹' P.family.domain

theorem sourceBetaDomain_open (P : HillHminusPsiChart) : IsOpen P.sourceBetaDomain :=
  P.analyticOnNhd_dirichletSource.continuousOn.isOpen_inter_preimage
    P.source_open P.family.domain_open

/-- Every real-form point of the original chart belongs to the common
source correction domain, without any open-gap restriction. -/
theorem mem_sourceBetaDomain_of_real (P : HillHminusPsiChart)
    (q : PeriodOneHminusOne) (hq : q∈P.source)
    (hreal : ∀ k : ℤ, P.miura.lift q (-k)=conj (P.miura.lift q k)) :
    q∈P.sourceBetaDomain :=
  ⟨hq,P.family.real_subset (isRealType_sourcePhase _
    (isRealType_hillMiuraDiagonal ⟨P.miura.lift q,hreal⟩))⟩

def sourceBetaCorrection (P : HillHminusPsiChart) (n : ℤ) (a : PeriodOneHminusOne) : ℂ :=
  sourceAngularBetaCorrection (by norm_num) (by norm_num) n P.family.roots (P.dirichletSource a)

def sourceBetaPartialSum (P : HillHminusPsiChart) (n : ℤ) (N : ℕ)
    (a : PeriodOneHminusOne) : ℂ :=
  ∑ m∈Finset.Icc (-(N:ℤ)) N,
    sourceAngularBetaSeriesTerm (by norm_num) (by norm_num) n P.family.roots (P.dirichletSource a) m

/-- The full actual signed source correction is analytic in the full
complex H-minus-one source variable, including collapsed gaps. -/
theorem analytic_sourceBetaCorrection (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots) (n : ℤ) :
    AnalyticOnNhd ℂ (P.sourceBetaCorrection n) P.sourceBetaDomain := by
  intro a ha
  exact (H.beta_original_series.analytic_correction n _ ha.2).comp
    (f := P.dirichletSource) (P.analyticOnNhd_dirichletSource a ha.1)

/-- ONE complex H-minus-one neighborhood precedes ALL signed omitted
indices in the local uniform convergence of the complete source series. -/
theorem exists_local_uniform_sourceBetaCorrection (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (q : PeriodOneHminusOne) (hq : q∈P.sourceBetaDomain) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q∈U ∧ U⊆P.sourceBetaDomain ∧
      ∀ n : ℤ, TendstoUniformlyOn (P.sourceBetaPartialSum n)
        (P.sourceBetaCorrection n) atTop U := by
  obtain ⟨V,hV,hqV,hVW,hconv⟩ := H.beta_original_series.locally_uniform (P.dirichletSource q) hq.2
  let U := P.sourceBetaDomain∩P.dirichletSource ⁻¹' V
  have hc : ContinuousOn P.dirichletSource P.sourceBetaDomain :=
    P.analyticOnNhd_dirichletSource.continuousOn.mono inter_subset_left
  refine ⟨U,hc.isOpen_inter_preimage P.sourceBetaDomain_open hV,⟨hq,hqV⟩,inter_subset_left,?_⟩
  intro n
  exact ((hconv n).comp P.dirichletSource).mono (fun a ha => ha.2)

/-- Absolute convergence is retained at every complex source. -/
theorem summable_norm_sourceBetaTerm (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (a : PeriodOneHminusOne) (ha : a∈P.sourceBetaDomain) (n : ℤ) :
    Summable (fun m : ℤ => ‖sourceAngularBetaSeriesTerm (by norm_num) (by norm_num)
      n P.family.roots (P.dirichletSource a) m‖) :=
  H.beta_original_series.summable_norm _ ha.2 n

/-- The actual complete source correction vanishes in both signed
index directions at every source of this common domain. -/
theorem sourceBetaCorrection_decay (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (a : PeriodOneHminusOne) (ha : a∈P.sourceBetaDomain) :
    Tendsto (fun n : ℤ => P.sourceBetaCorrection n a) cofinite (𝓝 0) :=
  H.beta_original_series.correction_decay _ ha.2

end NLS.KdV.HillHminusPsiChart
