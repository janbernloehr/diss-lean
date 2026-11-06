import NLS.KdV.HillHminusDirichletSourceBetaSeries
import NLS.SequenceSpaces.PairedPositiveOffIndexSeries

/-! The positive paired source correction, with BOTH selected signed
slots and the central slot removed. These are exactly the index sets
required by the scalar off-index construction. Identification of actual
scalar terminal primitive values remains separate from the series proof. -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat NLS.SequenceSpaces
namespace NLS.KdV.HillHminusPsiChart

def sourcePairedBetaTerm (P : HillHminusPsiChart) (n : ℕ+) (a : PeriodOneHminusOne) (j : ℕ) : ℂ :=
  pairedPositiveOffIndexTerm n (sourceAngularBetaSeriesTerm (by norm_num) (by norm_num)
    ((n:ℕ):ℤ) P.family.roots (P.dirichletSource a)) j

def sourcePairedBetaCorrection (P : HillHminusPsiChart) (n : ℕ+) (a : PeriodOneHminusOne) : ℂ :=
  ∑' j : ℕ, P.sourcePairedBetaTerm n a j

def sourcePairedBetaPartialSum (P : HillHminusPsiChart) (n : ℕ+) (N : ℕ)
    (a : PeriodOneHminusOne) : ℂ := ∑ j∈Finset.range N, P.sourcePairedBetaTerm n a j

theorem summable_norm_sourcePairedBetaTerm (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (n : ℕ+) (a : PeriodOneHminusOne) (ha : a∈P.sourceBetaDomain) :
    Summable (fun j : ℕ => ‖P.sourcePairedBetaTerm n a j‖) :=
  summable_norm_pairedPositiveOffIndexTerm n _ (P.summable_norm_sourceBetaTerm H a ha (n:ℕ))

/-- The correction differs from the complete signed source correction
by exactly the central and negative selected beta values. -/
theorem sourcePairedBetaCorrection_eq (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (n : ℕ+) (a : PeriodOneHminusOne) (ha : a∈P.sourceBetaDomain) :
    P.sourcePairedBetaCorrection n a=P.sourceBetaCorrection (n:ℕ) a-
      sourceAngularBeta (by norm_num) (by norm_num) ((n:ℕ):ℤ) 0 P.family.roots (P.dirichletSource a)-
      sourceAngularBeta (by norm_num) (by norm_num) ((n:ℕ):ℤ) (-((n:ℕ):ℤ))
        P.family.roots (P.dirichletSource a) := by
  have hn := n.pos
  have hzero : (0:ℤ)≠(n:ℕ) := by omega
  have hneg : -((n:ℕ):ℤ)≠(n:ℕ) := by omega
  rw [sourcePairedBetaCorrection]
  change (∑' j : ℕ, pairedPositiveOffIndexTerm n
    (sourceAngularBetaSeriesTerm (by norm_num) (by norm_num) ((n:ℕ):ℤ)
      P.family.roots (P.dirichletSource a)) j)=_
  rw [tsum_pairedPositiveOffIndexTerm n _ (P.summable_norm_sourceBetaTerm H a ha (n:ℕ))]
  simp only [sourceAngularBetaSeriesTerm,if_neg hzero,if_neg hneg,ite_true,sub_zero]
  rfl

/-- The paired positive correction is analytic on the SAME common
complex H-minus-one domain, with no selected-gap restriction. -/
theorem analytic_sourcePairedBetaCorrection (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots) (n : ℕ+) :
    AnalyticOnNhd ℂ (P.sourcePairedBetaCorrection n) P.sourceBetaDomain := by
  have hn := n.pos
  have hzero : (0:ℤ)≠(n:ℕ) := by omega
  have hneg : -((n:ℕ):ℤ)≠(n:ℕ) := by omega
  have han (m : ℤ) (hm : m≠(n:ℕ)) : AnalyticOnNhd ℂ
      (fun a => sourceAngularBeta (by norm_num) (by norm_num) ((n:ℕ):ℤ) m
        P.family.roots (P.dirichletSource a)) P.sourceBetaDomain := by
    intro a ha
    exact (H.beta_original_analytic ((n:ℕ):ℤ) m hm _ ha.2).comp
      (f := P.dirichletSource) (P.analyticOnNhd_dirichletSource a ha.1)
  have hh := ((P.analytic_sourceBetaCorrection H (n:ℕ)).sub (han 0 hzero)).sub (han _ hneg)
  apply hh.congr P.sourceBetaDomain_open
  intro a ha
  exact (P.sourcePairedBetaCorrection_eq H n a ha).symm

/-- ONE neighborhood precedes ALL positive omitted indices for the
locally uniform convergence of the actual paired positive series. -/
theorem exists_local_uniform_sourcePairedBetaCorrection (P : HillHminusPsiChart)
    (H : SourceLemma12_12Data (by norm_num) (by norm_num)
      P.family.originalDomain P.family.domain P.family.roots)
    (q : PeriodOneHminusOne) (hq : q∈P.sourceBetaDomain) :
    ∃ U : Set PeriodOneHminusOne, IsOpen U ∧ q∈U ∧ U⊆P.sourceBetaDomain ∧
      ∀ n : ℕ+, TendstoUniformlyOn (P.sourcePairedBetaPartialSum n)
        (P.sourcePairedBetaCorrection n) atTop U := by
  obtain ⟨U,hU,hqU,hUP,hconv⟩ := P.exists_local_uniform_sourceBetaCorrection H q hq
  refine ⟨U,hU,hqU,hUP,?_⟩
  intro n
  exact tendstoUniformlyOn_pairedPositiveOffIndexTerm n
    (fun a => sourceAngularBetaSeriesTerm (by norm_num) (by norm_num) ((n:ℕ):ℤ)
      P.family.roots (P.dirichletSource a)) U
    (fun a ha => P.summable_norm_sourceBetaTerm H a (hUP ha) (n:ℕ)) (hconv (n:ℕ))

end NLS.KdV.HillHminusPsiChart
