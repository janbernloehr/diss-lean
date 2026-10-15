import NLS.ZakharovShabat.SourceIndexedHigherActionSobolev
import NLS.ZakharovShabat.SourceHigherSobolevDenseInclusion
import NLS.ZakharovShabat.SobolevNLSHierarchyTrace
import NLS.ZakharovShabat.SobolevOddHamiltonianTrace

/-! # Physical traces on the full original complex Sobolev domain

Connectedness and real-form uniqueness extend physical identities to every
complex source in the unchanged Section 19 domain. The Hamiltonians retain
their independent Riccati definitions. No new neighborhood is selected.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ZakharovShabat
namespace SourceSection19Data
variable {W U : Set (CoeffPair 2)} (Q : SourceSection19Data (by simp) (by norm_num) W U)
include Q

theorem isConnected_higherSobolev_domain (s : ℕ) :
    IsConnected (higherSobolevSourceInclusion s ⁻¹' U) :=
  NLS.ComplexAnalysis.isConnected_preimage_dense_linear
    ((higherSobolevSourceInclusion s).restrictScalars ℝ).toLinearMap
    (higherSobolevSourceInclusion_denseRange s) Q.source_open Q.connected

theorem indexedHigherAction_trace_of_real (s k : ℕ) (hk : k ≤ 2*s)
    (H : SobolevSource s → ℂ) (hH : AnalyticOnNhd ℂ H univ)
    (hreal : ∀ a : realTypeHigherSobolevSourceLocus s,
      (∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n k
        (higherSobolevSourceInclusion s a.val)) = H a.val) :
    ∀ a : SobolevSource s, higherSobolevSourceInclusion s a ∈ U →
      (∑' n : ℤ, sourceIndexedHigherAction (by simp) (by norm_num) n k
        (higherSobolevSourceInclusion s a)) = H a := by
  let a₀ : realTypeHigherSobolevSourceLocus s := ⟨0,by simp [IsRealType]⟩
  have ha₀ : higherSobolevSourceInclusion s a₀.val ∈ U := Q.real_subset a₀.property
  have he : ∀ a : realTypeHigherSobolevSourceLocus s,
      (∑' n : ℤ, sourceIndexedHigherAction (by simp) (by norm_num) n k
        (higherSobolevSourceInclusion s a.val)) = H a.val := by
    intro a
    rw [← hreal a]
    apply tsum_congr
    intro n
    rw [sourceIndexedHigherAction_eq_real (by simp) (by norm_num) ⟨_,a.property⟩,
      sourceComplexHigherAction_eq_real (by simp) (by norm_num) ⟨_,a.property⟩]
  have hf := Q.analytic_tsum_indexedHigherAction s k hk
  have hg := eventuallyEq_higherSobolev_of_analyticAt_of_real_agreement s a₀ _ H
    (hf a₀.val ha₀) (hH a₀.val (mem_univ _)) he
  exact hf.eqOn_of_preconnected_of_eventuallyEq (hH.mono (subset_univ _))
    (Q.isConnected_higherSobolev_domain s).isPreconnected ha₀ hg

/-- Theorem 24.1 on the entire original complex Hˢ domain, through Hamiltonian order s+1. -/
theorem indexedHigherAction_hamiltonian_trace (s k : ℕ) (hk : k ≤ s)
    (a : SobolevSource s) (ha : higherSobolevSourceInclusion s a ∈ U) :
    (∑' n : ℤ, sourceIndexedHigherAction (by simp) (by norm_num) n k
      (higherSobolevSourceInclusion s a)) = sobolevNLSHamiltonian s a (k+1) (by omega)/2^k :=
  Q.indexedHigherAction_trace_of_real s k (by omega) _
    (fun b _ => (analyticAt_sobolevNLSHamiltonian s (k+1) (by omega) b).div_const)
    (sobolevNLSHamiltonian_higherAction_trace s k hk) a ha

/-- The sharp odd trace on the full original complex Hᵐ domain, with positive factor 4ᵐ. -/
theorem indexedHigherAction_oddHamiltonian_trace (m : ℕ) (hm : 1 ≤ m)
    (a : SobolevSource m) (ha : higherSobolevSourceInclusion m a ∈ U) :
    (∑' n : ℤ, sourceIndexedHigherAction (by simp) (by norm_num) n (2*m)
      (higherSobolevSourceInclusion m a)) = sobolevOddHamiltonian m hm a/4^m :=
  Q.indexedHigherAction_trace_of_real m (2*m) le_rfl _
    (fun b _ => (analyticAt_sobolevOddHamiltonian m hm b).div_const)
    (sobolevOddHamiltonian_higherAction_trace m hm) a ha
end SourceSection19Data
end NLS.ZakharovShabat
