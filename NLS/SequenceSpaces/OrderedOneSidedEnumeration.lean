import NLS.SequenceSpaces.OrderedFiniteEnumeration

/-! # An ordered finite block followed by ordered pairs

This is the one-sided indexing used by scalar second-order spectra: an
initial finite block, followed by two slots per high-frequency index.
-/

noncomputable section
namespace NLS

def appendPairedTail {α : Type*} (L : ℕ) (xi left right : ℕ → α) (j : ℕ) : α :=
  if j < L then xi j else
    if (j-L)%2 = 0 then left ((j-L)/2) else right ((j-L)/2)

theorem appendPairedTail_prefix {α : Type*} (L : ℕ) (xi left right : ℕ → α)
    (j : ℕ) (hj : j < L) : appendPairedTail L xi left right j = xi j := by
  simp only [appendPairedTail, if_pos hj]

theorem appendPairedTail_even {α : Type*} (L : ℕ) (xi left right : ℕ → α) (k : ℕ) :
    appendPairedTail L xi left right (L+2*k) = left k := by
  have hj : ¬L+2*k < L := by omega
  simp [appendPairedTail, hj]

theorem appendPairedTail_odd {α : Type*} (L : ℕ) (xi left right : ℕ → α) (k : ℕ) :
    appendPairedTail L xi left right (L+2*k+1) = right k := by
  have hj : ¬L+2*k+1 < L := by omega
  have hd : (L+2*k+1-L)/2 = k := by omega
  have hm : (L+2*k+1-L)%2 ≠ 0 := by omega
  simp only [appendPairedTail, if_neg hj, if_neg hm, hd]

/-- Ordering of the block, each pair, successive pairs and the junction
proves ordering of the entire one-sided sequence. -/
theorem monotone_appendPairedTail {α : Type*} [Preorder α]
    (L : ℕ) (xi left right : ℕ → α)
    (hxi : ∀ i < L, ∀ j < L, i ≤ j → xi i ≤ xi j)
    (hp : ∀ k, left k ≤ right k) (hn : ∀ k, right k ≤ left (k+1))
    (hj : ∀ j < L, xi j ≤ left 0) : Monotone (appendPairedTail L xi left right) := by
  apply monotone_nat_of_le_succ
  intro j
  by_cases h : j < L
  · by_cases h' : j+1 < L
    · rw [appendPairedTail_prefix L xi left right j h,
        appendPairedTail_prefix L xi left right (j+1) h']
      exact hxi j h (j+1) h' (by omega)
    · have he : j+1 = L := by omega
      rw [appendPairedTail_prefix L xi left right j h, he]
      have hh := appendPairedTail_even L xi left right 0
      simp only [mul_zero, add_zero] at hh
      rw [hh]
      exact hj j h
  · have h' : ¬j+1 < L := by omega
    simp only [appendPairedTail, if_neg h, if_neg h']
    have hd : j+1-L = (j-L)+1 := by omega
    rw [hd]
    by_cases hm : (j-L)%2 = 0
    · have hm' : ((j-L)+1)%2 ≠ 0 := by omega
      have hq : ((j-L)+1)/2 = (j-L)/2 := by omega
      rw [if_pos hm, if_neg hm', hq]
      exact hp _
    · have hm' : ((j-L)+1)%2 = 0 := by omega
      have hq : ((j-L)+1)/2 = (j-L)/2+1 := by omega
      rw [if_neg hm, if_pos hm', hq]
      exact hn _

end NLS
