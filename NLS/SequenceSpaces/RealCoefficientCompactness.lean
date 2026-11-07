import NLS.SequenceSpaces.CoefficientCompactness
import NLS.SequenceSpaces.PeriodOneMiuraRealLift

/-! Bounded physical REAL L2 coefficients have a subsequence with a REAL
L2 coefficient limit. No zero-mode restriction is imposed on the lifts. -/
noncomputable section
open Set Filter Topology Complex
namespace NLS

theorem exists_periodOneRealL2_coefficientwise_subseq (u : ℕ → PeriodOneRealL2)
    (hb : Bornology.IsBounded (range (fun k => (u k).val))) :
    ∃ v : PeriodOneRealL2, ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ j : ℤ, Tendsto (fun k => (u (σ k)).val j) atTop (𝓝 (v.val j)) := by
  obtain ⟨v,σ,hσ,ht⟩ := Coeff.exists_coefficientwise_tendsto_subseq_of_bounded (fun k => (u k).val) hb
  have hv : ∀ j : ℤ, v (-j)=(starRingEnd ℂ) (v j) := by
    intro j
    have hc := continuous_conj.continuousAt.tendsto.comp (ht j)
    have he : (fun k => (u (σ k)).val (-j))=(fun k => (starRingEnd ℂ) ((u (σ k)).val j)) :=
      funext (fun k => (u (σ k)).property j)
    change Tendsto (fun k => (starRingEnd ℂ) ((u (σ k)).val j)) atTop (𝓝 ((starRingEnd ℂ) (v j))) at hc
    rw [← he] at hc
    exact tendsto_nhds_unique (ht (-j)) hc
  exact ⟨⟨v,hv⟩,σ,hσ,ht⟩

end NLS
