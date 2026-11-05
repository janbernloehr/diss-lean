import NLS.ComplexAnalysis.ZeroMultiset

/-! # Matching multiplicities in a two-zero cluster

Two nontrivial analytic functions with the same zero set and total count
two have identical orders in the cluster, including at a collision.
-/

noncomputable section
open Set
open scoped Classical
namespace NLS.ComplexAnalysis

/-- A cluster of total multiplicity two has its orders determined by its
zero set. The nontriviality hypotheses ensure all orders are finite. -/
theorem analyticOrderNatAt_eq_of_two_zero_counts
    {f g : ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K) (hconn : IsConnected K)
    (hf : AnalyticOnNhd ℂ f K) (hg : AnalyticOnNhd ℂ g K)
    {b : ℂ} (hb : b ∈ K) (hfb : f b ≠ 0) (hgb : g b ≠ 0)
    (hfc : analyticZeroCount f K = 2) (hgc : analyticZeroCount g K = 2)
    (hzeros : ∀ z ∈ K, f z = 0 ↔ g z = 0) {z : ℂ} (hz : z ∈ K) :
    analyticOrderNatAt f z = analyticOrderNatAt g z := by
  obtain ⟨a,ha,c,hc,hfa,hfc',hpair⟩ := exists_two_analytic_zeros
    (analyticZeroCount_hasFiniteSupport hK hconn hf hb hfb) hfc
  obtain ⟨u,hu,v,hv,hgu,hgv,hpair'⟩ := exists_two_analytic_zeros
    (analyticZeroCount_hasFiniteSupport hK hconn hg hb hgb) hgc
  have hfset (w : ℂ) : (w ∈ K ∧ f w = 0) ↔ w ∈ ({a,c} : Set ℂ) := by
    constructor
    · rintro ⟨hw,hw0⟩
      have hp := analyticOrderNatAt_pos_of_zero (hf w hw)
        (analyticOrderAt_ne_top_on_connected hconn.isPreconnected hf hb hfb hw) hw0
      have hp' : 0 < ({a,c} : Multiset ℂ).count w := by
        rw [← hpair w, if_pos hw]
        exact hp
      simpa using Multiset.count_pos.mp hp'
    · rintro (rfl | rfl)
      · exact ⟨ha,hfa⟩
      · exact ⟨hc,hfc'⟩
  have hgset (w : ℂ) : (w ∈ K ∧ g w = 0) ↔ w ∈ ({u,v} : Set ℂ) := by
    constructor
    · rintro ⟨hw,hw0⟩
      have hp := analyticOrderNatAt_pos_of_zero (hg w hw)
        (analyticOrderAt_ne_top_on_connected hconn.isPreconnected hg hb hgb hw) hw0
      have hp' : 0 < ({u,v} : Multiset ℂ).count w := by
        rw [← hpair' w, if_pos hw]
        exact hp
      simpa using Multiset.count_pos.mp hp'
    · rintro (rfl | rfl)
      · exact ⟨hu,hgu⟩
      · exact ⟨hv,hgv⟩
  have hset : ({a,c} : Set ℂ) = {u,v} := by
    ext w
    rw [← hfset, ← hgset]
    exact and_congr_right (hzeros w)
  have hp : ({a,c} : Multiset ℂ) = {u,v} := by
    rcases Set.pair_eq_pair_iff.mp hset with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rfl
    · exact Multiset.pair_comm _ _
  have he := (hpair z).trans ((congrArg (fun s : Multiset ℂ => s.count z) hp).trans
    (hpair' z).symm)
  simpa only [if_pos hz] using he

end NLS.ComplexAnalysis
