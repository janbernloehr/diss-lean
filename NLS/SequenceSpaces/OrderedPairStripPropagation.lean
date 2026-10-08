import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Set.Basic

/-! # Propagating ordered pairs across adjacent counted intervals

Exactly two occurrences in each adjacent interval determine the preceding
or following pair from an anchored pair. Values may repeat; indices do not.
-/
open scoped Classical
namespace NLS

/-- Two known occurrences exhaust a finite set of cardinality two. -/
theorem not_mem_of_card_two {ι : Type*} (s : Finset ι) (hs : s.card = 2)
    {a b c : ι} (hb : b ∈ s) (hc : c ∈ s) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : a ∉ s := by
  intro ha
  have hsub : ({a,b,c} : Finset ι) ⊆ s := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have ht : ({a,b,c} : Finset ι).card = 3 := by simp [hab,hac,hbc]
  have h := Finset.card_le_card hsub
  omega

/-- An anchored right pair forces its immediate predecessor into the preceding counted interval. -/
theorem ordered_pair_step_left {ι α : Type*} [LinearOrder ι] [LinearOrder α]
    (s : Finset ι) (f : ι → α) (hf : MonotoneOn f (s : Set ι))
    (a b c d : ι) (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hbetween : ∀ k, a < k → k < c → k = b)
    (l m r : α)
    (hleft : (s.filter (fun k => f k ∈ Set.Icc l m)).card = 2)
    (hright : (s.filter (fun k => f k ∈ Set.Icc m r)).card = 2)
    (hcm : m < f c) (hcr : f c ≤ r) (hdm : m ≤ f d) (hdr : f d ≤ r) :
    f a ∈ Set.Icc l m ∧ f b ∈ Set.Icc l m := by
  have hbm : f b < m := by
    by_contra h
    have hm : m ≤ f b := le_of_not_gt h
    have hbmem : b ∈ s.filter (fun k => f k ∈ Set.Icc m r) :=
      Finset.mem_filter.mpr ⟨hb,hm,(hf hb hc hbc.le).trans hcr⟩
    exact not_mem_of_card_two _ hright
      (Finset.mem_filter.mpr ⟨hc,hcm.le,hcr⟩) (Finset.mem_filter.mpr ⟨hd,hdm,hdr⟩)
      hbc.ne (hbc.trans hcd).ne hcd.ne hbmem
  have hla : l ≤ f a := by
    by_contra h
    have hal : f a < l := lt_of_not_ge h
    have hsub : s.filter (fun k => f k ∈ Set.Icc l m) ⊆ {b} := by
      intro k hk
      obtain ⟨hks,hlk,hkm⟩ := Finset.mem_filter.mp hk
      apply Finset.mem_singleton.mpr
      apply hbetween k
      · by_contra hka
        exact ((hf hks ha (le_of_not_gt hka)).trans_lt hal).not_ge hlk
      · by_contra hck
        exact (hcm.trans_le (hf hc hks (le_of_not_gt hck))).not_ge hkm
    have hh := Finset.card_le_card hsub
    simp only [hleft, Finset.card_singleton] at hh
    omega
  exact ⟨⟨hla,(hf ha hb hab.le).trans hbm.le⟩,⟨hla.trans (hf ha hb hab.le),hbm.le⟩⟩

/-- The order-dual argument propagates an anchored left pair to its immediate successor. -/
theorem ordered_pair_step_right {ι α : Type*} [LinearOrder ι] [LinearOrder α]
    (s : Finset ι) (f : ι → α) (hf : MonotoneOn f (s : Set ι))
    (a b c d : ι) (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s)
    (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hbetween : ∀ k, b < k → k < d → k = c)
    (l m r : α)
    (hleft : (s.filter (fun k => f k ∈ Set.Icc l m)).card = 2)
    (hright : (s.filter (fun k => f k ∈ Set.Icc m r)).card = 2)
    (hal : l ≤ f a) (ham : f a ≤ m) (hbl : l ≤ f b) (hbm : f b < m) :
    f c ∈ Set.Icc m r ∧ f d ∈ Set.Icc m r := by
  have h := ordered_pair_step_left (ι := ιᵒᵈ) (α := αᵒᵈ) s f
    (fun _ hi _ hj hij => hf hj hi hij) d c b a hd hc hb ha hcd hbc hab
    (fun k hkd hbk => hbetween k hbk hkd) r m l
    (by
      change (s.filter (fun k => f k ≤ r ∧ m ≤ f k)).card = 2
      simpa only [Set.mem_Icc, and_comm] using hright)
    (by
      change (s.filter (fun k => f k ≤ m ∧ l ≤ f k)).card = 2
      simpa only [Set.mem_Icc, and_comm] using hleft) hbm hbl ham hal
  exact ⟨⟨h.2.2,h.2.1⟩,⟨h.1.2,h.1.1⟩⟩

end NLS
