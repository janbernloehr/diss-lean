import NLS.SequenceSpaces.CoefficientCompactness

/-! # Simultaneous disjoint block approximations

Two coefficient-null sequences at finite Banach exponents admit one common
subsequence and disjoint finite blocks, with any prescribed positive
errors. No norm bounds on the sequences are needed for the construction.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Approximate a sufficiently late pair by one finite block beyond a
prescribed head, while extending that head for the next step. -/
theorem exists_simultaneous_block (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (x : ℕ → Coeff p) (y : ℕ → Coeff q)
    (hx : ∀ n, Tendsto (fun k => x k n) atTop (𝓝 0))
    (hy : ∀ n, Tendsto (fun k => y k n) atTop (𝓝 0))
    (S : Finset ℤ) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∃ U : Finset ℤ, S ⊆ U ∧ N ≤ k ∧
      ‖x k-truncate (U \ S) (x k)‖ < ε ∧ ‖y k-truncate (U \ S) (y k)‖ < ε := by
  have hxs : Tendsto (fun k => ‖truncate S (x k)‖) atTop (𝓝 0) := by
    simpa [truncate] using (tendsto_truncate_of_coefficientwise x 0 (by simpa using hx) S).norm
  have hys : Tendsto (fun k => ‖truncate S (y k)‖) atTop (𝓝 0) := by
    simpa [truncate] using (tendsto_truncate_of_coefficientwise y 0 (by simpa using hy) S).norm
  obtain ⟨k,hk,hxk,hyk⟩ := ((eventually_ge_atTop N).and
    ((hxs.eventually (gt_mem_nhds (half_pos hε))).and
      (hys.eventually (gt_mem_nhds (half_pos hε))))).exists
  obtain ⟨U₁,hU₁⟩ := Metric.tendsto_atTop.mp (tendsto_truncate hp (x k)) (ε/2) (half_pos hε)
  obtain ⟨U₂,hU₂⟩ := Metric.tendsto_atTop.mp (tendsto_truncate hq (y k)) (ε/2) (half_pos hε)
  let U := S ∪ U₁ ∪ U₂
  have hSU : S ⊆ U := (Finset.subset_union_left).trans Finset.subset_union_left
  have h₁ : U₁ ⊆ U := (Finset.subset_union_right).trans Finset.subset_union_left
  have h₂ : U₂ ⊆ U := Finset.subset_union_right
  have he {r : ℝ≥0∞} (a : Coeff r) : a-truncate (U \ S) a = (a-truncate U a)+truncate S a := by
    ext n
    by_cases hn : n ∈ S
    · simp [truncate_apply,hn,hSU hn]
    · by_cases hnU : n ∈ U <;> simp [truncate_apply,hn,hnU]
  refine ⟨k,U,hSU,hk,?_,?_⟩
  · rw [he]
    have ht := hU₁ U h₁
    rw [dist_eq_norm,norm_sub_rev] at ht
    exact (norm_add_le _ _).trans_lt (by linarith)
  · rw [he]
    have ht := hU₂ U h₂
    rw [dist_eq_norm,norm_sub_rev] at ht
    exact (norm_add_le _ _).trans_lt (by linarith)

/-- A common subsequence has disjoint finite approximations in both
sequence spaces, with arbitrarily small prescribed errors at every step. -/
theorem exists_simultaneous_disjoint_blocks (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    (x : ℕ → Coeff p) (y : ℕ → Coeff q)
    (hx : ∀ n, Tendsto (fun k => x k n) atTop (𝓝 0))
    (hy : ∀ n, Tendsto (fun k => y k n) atTop (𝓝 0))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ S : ℕ → Finset ℤ,
      Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      ∀ n, ‖x (σ n)-truncate (S n) (x (σ n))‖ < ε n ∧
        ‖y (σ n)-truncate (S n) (y (σ n))‖ < ε n := by
  classical
  choose k U hsub hk herr using
    (fun n (a : ℕ × Finset ℤ) => exists_simultaneous_block hp hq x y hx hy a.2 (a.1+1) (ε n) (hε n))
  let a : ℕ → ℕ × Finset ℤ := Nat.rec (0,∅) (fun n a => (k n a,U n a))
  let σ (n : ℕ) := k n (a n)
  let H (n : ℕ) := (a n).2
  have hstep (n : ℕ) : H n ⊆ H (n+1) := hsub n (a n)
  have hmono : Monotone H := monotone_nat_of_le_succ hstep
  have hσ : StrictMono σ := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact lt_of_lt_of_le (Nat.lt_succ_self (σ n)) (hk (n+1) (a (n+1)))
  let S (n : ℕ) := H (n+1) \ H n
  have hd (i j : ℕ) (hij : i < j) : Disjoint (S i) (S j) := by
    apply Finset.disjoint_left.mpr
    intro n hni hnj
    exact (Finset.mem_sdiff.mp hnj).2
      (hmono (Nat.succ_le_iff.mpr hij) (Finset.mem_sdiff.mp hni).1)
  refine ⟨σ,hσ,S,?_,?_⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hd i j h
    · exact (hd j i h).symm
  · intro n
    exact herr n (a n)

end NLS.Coeff
