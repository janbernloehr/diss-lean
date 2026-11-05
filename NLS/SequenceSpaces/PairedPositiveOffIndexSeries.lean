import NLS.SequenceSpaces.IntegerSymmetricSums
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.UniformSpace.UniformConvergence

noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace NLS.SequenceSpaces

/-- Pair the positive and negative signed slots, deleting BOTH slots
of the selected positive index and deleting the central slot zero. -/
def pairedPositiveOffIndexTerm (n : ℕ+) (f : ℤ → ℂ) (j : ℕ) : ℂ :=
  if (j:ℤ)+1=(n:ℕ) then 0 else f ((j:ℤ)+1)+f (-((j:ℤ)+1))

theorem sum_pairedPositiveOffIndexTerm (n : ℕ+) (f : ℤ → ℂ)
    (N : ℕ) (hN : (n:ℕ)≤N) :
    (∑ j∈Finset.range N, pairedPositiveOffIndexTerm n f j)=
      (∑ k∈Finset.Icc (-(N:ℤ)) N, f k)-f 0-f (n:ℕ)-f (-((n:ℕ):ℤ)) := by
  have hn := n.pos
  let k : ℕ := (n:ℕ)-1
  let h : ℕ → ℂ := fun j => f ((j:ℤ)+1)+f (-((j:ℤ)+1))
  have hk : k<N := by dsimp only [k]; omega
  have hindex : (k:ℤ)+1=(n:ℕ) := by dsimp only [k]; omega
  have he (j : ℕ) : pairedPositiveOffIndexTerm n f j=h j-(if j=k then h k else 0) := by
    by_cases hj : j=k
    · subst j
      simp [pairedPositiveOffIndexTerm,hindex]
    · have hjn : (j:ℤ)+1≠(n:ℕ) := by intro hh; apply hj; dsimp only [k]; omega
      simp only [pairedPositiveOffIndexTerm,if_neg hjn,if_neg hj,sub_zero,h]
  simp_rw [he]
  rw [Finset.sum_sub_distrib,Finset.sum_ite_eq',if_pos (Finset.mem_range.mpr hk),sum_symmetric_interval]
  change (∑ j∈Finset.range N, h j)-h k=
    f 0+(∑ j∈Finset.range N, h j)-f 0-f (n:ℕ)-f (-((n:ℕ):ℤ))
  dsimp only [h]
  rw [hindex]
  ring

theorem summable_norm_pairedPositiveOffIndexTerm (n : ℕ+) (f : ℤ → ℂ)
    (hf : Summable (fun k : ℤ => ‖f k‖)) :
    Summable (fun j : ℕ => ‖pairedPositiveOffIndexTerm n f j‖) := by
  have hp : Summable (fun j : ℕ => ‖f ((j:ℤ)+1)‖) :=
    hf.comp_injective (show Function.Injective (fun j : ℕ => (j:ℤ)+1) from by intro a b h; change (a:ℤ)+1=(b:ℤ)+1 at h; omega)
  have hm : Summable (fun j : ℕ => ‖f (-((j:ℤ)+1))‖) :=
    hf.comp_injective (show Function.Injective (fun j : ℕ => -((j:ℤ)+1)) from by intro a b h; change -((a:ℤ)+1)=-((b:ℤ)+1) at h; omega)
  apply (hp.add hm).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro j
  unfold pairedPositiveOffIndexTerm
  split_ifs
  · simp only [norm_zero]
    positivity
  · exact norm_add_le _ _

/-- The full paired positive correction is the signed sum with exactly
its central and two selected signed slots removed. -/
theorem tsum_pairedPositiveOffIndexTerm (n : ℕ+) (f : ℤ → ℂ)
    (hf : Summable (fun k : ℤ => ‖f k‖)) :
    (∑' j : ℕ, pairedPositiveOffIndexTerm n f j)=
      (∑' k : ℤ, f k)-f 0-f (n:ℕ)-f (-((n:ℕ):ℤ)) := by
  have hn := n.pos
  let k : ℕ := (n:ℕ)-1
  let h : ℕ → ℂ := fun j => f ((j:ℤ)+1)+f (-((j:ℤ)+1))
  have hp : Summable (fun j : ℕ => f ((j:ℤ)+1)) :=
    hf.of_norm.comp_injective (show Function.Injective (fun j : ℕ => (j:ℤ)+1) from by intro a b h; change (a:ℤ)+1=(b:ℤ)+1 at h; omega)
  have hm : Summable (fun j : ℕ => f (-((j:ℤ)+1))) :=
    hf.of_norm.comp_injective (show Function.Injective (fun j : ℕ => -((j:ℤ)+1)) from by intro a b h; change -((a:ℤ)+1)=-((b:ℤ)+1) at h; omega)
  have hindex : (k:ℤ)+1=(n:ℕ) := by dsimp only [k]; omega
  have he : pairedPositiveOffIndexTerm n f=(fun j => h j-(if j=k then h k else 0)) := by
    funext j
    by_cases hj : j=k
    · subst j
      simp [pairedPositiveOffIndexTerm,hindex]
    · have hjn : (j:ℤ)+1≠(n:ℕ) := by intro hh; apply hj; dsimp only [k]; omega
      simp only [pairedPositiveOffIndexTerm,if_neg hjn,if_neg hj,sub_zero,h]
  rw [he,(hp.add hm).tsum_sub (hasSum_ite_eq k (h k)).summable,tsum_ite_eq,
    hp.tsum_add hm,tsum_of_add_one_of_neg_add_one hp hm]
  dsimp only [h]
  rw [hindex]
  ring

/-- Absolute signed series with uniform symmetric cutoffs give uniform
positive paired off-index series on the SAME parameter set. -/
theorem tendstoUniformlyOn_pairedPositiveOffIndexTerm {X : Type*}
    (n : ℕ+) (f : X → ℤ → ℂ) (U : Set X)
    (hf : ∀ a∈U, Summable (fun k : ℤ => ‖f a k‖))
    (hconv : TendstoUniformlyOn
      (fun (N : ℕ) a => ∑ k∈Finset.Icc (-(N:ℤ)) N, f a k)
      (fun a => ∑' k : ℤ, f a k) atTop U) :
    TendstoUniformlyOn
      (fun (N : ℕ) a => ∑ j∈Finset.range N, pairedPositiveOffIndexTerm n (f a) j)
      (fun a => ∑' j : ℕ, pairedPositiveOffIndexTerm n (f a) j) atTop U := by
  rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
  intro ε hε
  filter_upwards [hconv ε hε,eventually_ge_atTop (n:ℕ)] with N hbound hN
  intro a ha
  simpa only [sum_pairedPositiveOffIndexTerm n (f a) N hN,
    tsum_pairedPositiveOffIndexTerm n (f a) (hf a ha),dist_sub_right] using hbound a ha

end NLS.SequenceSpaces
