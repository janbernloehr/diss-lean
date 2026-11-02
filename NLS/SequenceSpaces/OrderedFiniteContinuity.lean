import NLS.SequenceSpaces.OrderedFiniteEnumeration
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-! # Continuity of finite ordered values from cumulative counts

For an ordered finite list, the number of entries below a threshold fixes
which side of that threshold each slot occupies. Stability of these
counts away from the limiting values therefore gives continuity, including
at repeated entries.
-/

noncomputable section
open Set Filter Topology
open scoped Classical
namespace NLS

def finiteLowerCount (L : ℕ) (xi : ℕ → ℝ) (b : ℝ) : ℕ :=
  ((Finset.range L).filter (fun j => xi j ≤ b)).card

theorem finiteLowerCount_le_iff (L : ℕ) (xi : ℕ → ℝ)
    (ho : ∀ i < L, ∀ j < L, i ≤ j → xi i ≤ xi j) (j : ℕ) (hj : j < L) (b : ℝ) :
    finiteLowerCount L xi b ≤ j ↔ b < xi j := by
  constructor
  · intro hc
    by_contra! hx
    have hs : Finset.range (j+1) ⊆ (Finset.range L).filter (fun i => xi i ≤ b) := by
      intro i hi
      have hij : i ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        (ho i (by omega) j hj hij).trans hx⟩
    have hh := Finset.card_le_card hs
    simp only [Finset.card_range] at hh
    change j+1 ≤ finiteLowerCount L xi b at hh
    omega
  · intro hb
    have hs : (Finset.range L).filter (fun i => xi i ≤ b) ⊆ Finset.range j := by
      intro i hi
      obtain ⟨hiL,hib⟩ := Finset.mem_filter.mp hi
      have hiL' := Finset.mem_range.mp hiL
      apply Finset.mem_range.mpr
      by_contra! hji
      exact (hb.trans_le (ho j hj i hiL' hji)).not_ge hib
    simpa only [finiteLowerCount, Finset.card_range] using Finset.card_le_card hs

theorem index_lt_finiteLowerCount_iff (L : ℕ) (xi : ℕ → ℝ)
    (ho : ∀ i < L, ∀ j < L, i ≤ j → xi i ≤ xi j) (j : ℕ) (hj : j < L) (b : ℝ) :
    j < finiteLowerCount L xi b ↔ xi j ≤ b := by
  simpa only [not_le, not_lt] using not_congr (finiteLowerCount_le_iff L xi ho j hj b)

/-- Stable cumulative counts away from the limiting finite values imply
convergence of each ordered slot, with repetitions permitted. -/
theorem tendsto_ordered_finite_of_counts
    {T : Type*} {l : Filter T} (L : ℕ) (xi : T → ℕ → ℝ) (eta : ℕ → ℝ) (a b : ℝ)
    (hxi : ∀ t, ∀ i < L, ∀ j < L, i ≤ j → xi t i ≤ xi t j)
    (heta : ∀ i < L, ∀ j < L, i ≤ j → eta i ≤ eta j)
    (hmem : ∀ j < L, eta j ∈ Ioo a b)
    (hc : ∀ c ∈ Ioo a b, c ∉ (Finset.range L).image eta →
      ∀ᶠ t in l, finiteLowerCount L (xi t) c = finiteLowerCount L eta c)
    (j : ℕ) (hj : j < L) : Tendsto (fun t => xi t j) l (𝓝 (eta j)) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon hepsilon
  have hleft : max a (eta j-epsilon) < eta j := max_lt (hmem j hj).1 (by linarith)
  have hright : eta j < min b (eta j+epsilon) := lt_min (hmem j hj).2 (by linarith)
  obtain ⟨c,hcI,hcnot⟩ := (Set.Ioo_infinite hleft).exists_notMem_finset ((Finset.range L).image eta)
  obtain ⟨d,hdI,hdnot⟩ := (Set.Ioo_infinite hright).exists_notMem_finset ((Finset.range L).image eta)
  have hcB : c ∈ Ioo a b := ⟨lt_of_le_of_lt (le_max_left _ _) hcI.1,hcI.2.trans (hmem j hj).2⟩
  have hdB : d ∈ Ioo a b := ⟨(hmem j hj).1.trans hdI.1,lt_of_lt_of_le hdI.2 (min_le_left _ _)⟩
  filter_upwards [hc c hcB hcnot,hc d hdB hdnot] with t htc htd
  have hcl : finiteLowerCount L (xi t) c ≤ j := by
    rw [htc]
    exact (finiteLowerCount_le_iff L eta heta j hj c).mpr hcI.2
  have hdr : j < finiteLowerCount L (xi t) d := by
    rw [htd]
    exact (index_lt_finiteLowerCount_iff L eta heta j hj d).mpr hdI.1.le
  have hxc := (finiteLowerCount_le_iff L (xi t) (hxi t) j hj c).mp hcl
  have hxd := (index_lt_finiteLowerCount_iff L (xi t) (hxi t) j hj d).mp hdr
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor
  · linarith [lt_of_le_of_lt (le_max_right a (eta j-epsilon)) hcI.1]
  · linarith [lt_of_lt_of_le hdI.2 (min_le_right b (eta j+epsilon))]

end NLS
