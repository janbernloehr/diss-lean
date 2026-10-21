import Mathlib.Data.Int.Interval
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
noncomputable section
open Set
namespace NLS.ZakharovShabat

/-- The printed one-based ordering: 0,-1,1,-2,2,... . Index zero is unused. -/
def section17Mode (k : ℕ) : ℤ :=
  if k%2=0 then -(k/2 : ℕ) else (k/2 : ℕ)

@[simp] theorem section17Mode_natAbs (k : ℕ) : (section17Mode k).natAbs = k/2 := by
  unfold section17Mode
  split_ifs <;> simp only [Int.natAbs_neg,Int.natAbs_natCast]

@[simp] theorem section17Mode_odd (j : ℕ) : section17Mode (2*j+1) = (j : ℤ) := by
  simp [section17Mode,Nat.add_div]

@[simp] theorem section17Mode_even (j : ℕ) : section17Mode (2*j) = -(j : ℤ) := by
  simp [section17Mode]

/-- The absolute-index cutoff N corresponds to 2N+1 enumeration positions. -/
theorem section17Mode_tail_iff (N k : ℕ) :
    N < (section17Mode k).natAbs ↔ 2*N+1 < k := by
  rw [section17Mode_natAbs]
  omega

/-- The corrected finite selection covers exactly all modes with absolute index at most N. -/
theorem section17Mode_initial_block (N : ℕ) :
    section17Mode '' {k : ℕ | 1 ≤ k ∧ k ≤ 2*N+1} = {n : ℤ | n.natAbs ≤ N} := by
  ext n
  constructor
  · rintro ⟨k,⟨_,hk⟩,rfl⟩
    change (section17Mode k).natAbs ≤ N
    rw [section17Mode_natAbs]
    omega
  · intro hn
    change n.natAbs ≤ N at hn
    cases n with
    | ofNat j =>
      have hj : j ≤ N := hn
      exact ⟨2*j+1,⟨by omega,by omega⟩,section17Mode_odd j⟩
    | negSucc j =>
      have hj : j+1 ≤ N := hn
      refine ⟨2*(j+1),⟨by omega,by omega⟩,?_⟩
      rw [section17Mode_even]
      omega

/-- The printed cutoff at N=1 leaves the positive first mode unreduced. -/
theorem section17Mode_eq_one_iff (k : ℕ) : section17Mode k = 1 ↔ k=3 := by
  unfold section17Mode
  split_ifs with hk <;> omega

/-- Shifting the one-based indexing gives a genuine enumeration of all integer modes. -/
theorem section17Mode_bijective : Function.Bijective (fun j : ℕ => section17Mode (j+1)) := by
  constructor
  · intro j k he
    dsimp only [section17Mode] at he
    split_ifs at he <;> omega
  · intro n
    cases n with
    | ofNat j => exact ⟨2*j,section17Mode_odd j⟩
    | negSucc j =>
      refine ⟨2*j+1,?_⟩
      change section17Mode (2*j+1+1) = Int.negSucc j
      rw [show 2*j+1+1=2*(j+1) by omega,section17Mode_even]
      omega

/-- The corrected enumeration tail is exactly the absolute-mode tail, for arbitrary data. -/
theorem section17Mode_corrected_tail_sum (N : ℕ) (f : ℤ → ℝ) :
    (∑' j : ℕ, if 2*N+1 < j+1 then f (section17Mode (j+1)) else 0) =
      ∑' n : ℤ, if N < n.natAbs then f n else 0 := by
  let e : ℕ ≃ ℤ := Equiv.ofBijective (fun j => section17Mode (j+1)) section17Mode_bijective
  have he := e.tsum_eq (fun n : ℤ => if N<n.natAbs then f n else 0)
  convert he using 1
  apply tsum_congr
  intro j
  change (if 2*N+1<j+1 then f (section17Mode (j+1)) else 0) =
    (if N<(section17Mode (j+1)).natAbs then f (section17Mode (j+1)) else 0)
  simp only [section17Mode_tail_iff]

end NLS.ZakharovShabat
