import NLS.SequenceSpaces.PositiveScalarExtension
import Mathlib.Tactic.Ring

/-! Exact pairing of literal symmetric integer cutoffs into positive
indices, retaining the central term and zero extension convention. -/
noncomputable section
open Set
open scoped Classical
namespace NLS.LpSequence

theorem positiveScalarExtension_eq_zero_of_nonpos (u : ℕ+ → ℂ) (j : ℤ) (hj : j ≤ 0) :
    positiveScalarExtension u j = 0 := by
  apply positiveScalarExtension_zero_of_not_mem_range
  rintro ⟨m,hm⟩
  change ((m:ℕ):ℤ) = j at hm
  have hpos : (0:ℤ) < ((m:ℕ):ℤ) := by exact_mod_cast m.pos
  omega

theorem sum_symmetricCutoff_succ (f : ℤ → ℂ) (N : ℕ) :
    (∑ j ∈ Finset.Icc (-((N+1:ℕ):ℤ)) ((N+1:ℕ):ℤ), f j) =
      f (-((N+1:ℕ):ℤ))+f ((N+1:ℕ):ℤ)+∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), f j := by
  have hs : Finset.Icc (-((N+1:ℕ):ℤ)) ((N+1:ℕ):ℤ) =
      insert (-((N+1:ℕ):ℤ)) (insert ((N+1:ℕ):ℤ) (Finset.Icc (-(N:ℤ)) (N:ℤ))) := by
    ext j
    simp only [Finset.mem_Icc,Finset.mem_insert]
    omega
  rw [hs,Finset.sum_insert (by simp only [Finset.mem_insert,Finset.mem_Icc]; omega),
    Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  ring

theorem positiveScalarExtension_const_mul (u : ℕ+ → ℂ) (c : ℂ) (j : ℤ) :
    positiveScalarExtension (fun m => c*u m) j = c*positiveScalarExtension u j := by
  by_cases hj : j ∈ range positiveEmbedding
  · obtain ⟨m,rfl⟩ := hj
    change positiveScalarExtension (fun m => c*u m) ((m:ℕ):ℤ) = c*positiveScalarExtension u ((m:ℕ):ℤ)
    rw [positiveScalarExtension_apply,positiveScalarExtension_apply]
  · rw [positiveScalarExtension_zero_of_not_mem_range _ j hj,
      positiveScalarExtension_zero_of_not_mem_range _ j hj,mul_zero]

theorem sum_symmetricCutoff_eq_central_add_positive_pairs (f : ℤ → ℂ) (N : ℕ) :
    (∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), f j) = f 0+
      ∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
        positiveScalarExtension (fun m : ℕ+ => f ((m:ℕ):ℤ)+f (-((m:ℕ):ℤ))) j := by
  induction N with
  | zero =>
    simp only [Nat.cast_zero,neg_zero,Finset.Icc_self,Finset.sum_singleton]
    rw [positiveScalarExtension_eq_zero_of_nonpos _ 0 le_rfl,add_zero]
  | succ N ih =>
    rw [sum_symmetricCutoff_succ f N,
      sum_symmetricCutoff_succ (positiveScalarExtension (fun m : ℕ+ => f ((m:ℕ):ℤ)+f (-((m:ℕ):ℤ)))) N,ih]
    rw [positiveScalarExtension_eq_zero_of_nonpos _ (-((N+1:ℕ):ℤ)) (by omega)]
    let m : ℕ+ := ⟨N+1,by omega⟩
    have hp : positiveScalarExtension (fun m : ℕ+ => f ((m:ℕ):ℤ)+f (-((m:ℕ):ℤ))) ((N+1:ℕ):ℤ) =
        f ((N+1:ℕ):ℤ)+f (-((N+1:ℕ):ℤ)) := positiveScalarExtension_apply _ m
    rw [hp]
    ring

theorem sum_positive_symmetricCutoff_reinsert_diagonal (u : ℕ+ → ℂ) (n : ℕ+)
    (N : ℕ) (hN : (n:ℕ) ≤ N) :
    (∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), positiveScalarExtension u j) = u n+
      ∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
        positiveScalarExtension (fun m : ℕ+ => if m=n then 0 else u m) j := by
  have he (j : ℤ) : positiveScalarExtension u j =
      (if j=((n:ℕ):ℤ) then u n else 0)+
        positiveScalarExtension (fun m : ℕ+ => if m=n then 0 else u m) j := by
    by_cases hj : j ∈ range positiveEmbedding
    · obtain ⟨m,rfl⟩ := hj
      change positiveScalarExtension u ((m:ℕ):ℤ) =
        (if ((m:ℕ):ℤ)=((n:ℕ):ℤ) then u n else 0)+
          positiveScalarExtension (fun m : ℕ+ => if m=n then 0 else u m) ((m:ℕ):ℤ)
      rw [positiveScalarExtension_apply,positiveScalarExtension_apply]
      by_cases hmn : m=n
      · subst m
        simp
      · have hjn : ((m:ℕ):ℤ) ≠ ((n:ℕ):ℤ) := by exact_mod_cast hmn
        simp only [if_neg hmn,if_neg hjn,zero_add]
    · have hjn : j ≠ ((n:ℕ):ℤ) := by intro he; apply hj; rw [he]; exact ⟨n,rfl⟩
      rw [positiveScalarExtension_zero_of_not_mem_range _ j hj,
        positiveScalarExtension_zero_of_not_mem_range _ j hj,if_neg hjn,zero_add]
  have hmem : ((n:ℕ):ℤ) ∈ Finset.Icc (-(N:ℤ)) (N:ℤ) := by
    simp only [Finset.mem_Icc]
    have := n.pos
    constructor <;> omega
  calc
    _ = ∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ),
        ((if j=((n:ℕ):ℤ) then u n else 0)+
          positiveScalarExtension (fun m : ℕ+ => if m=n then 0 else u m) j) :=
      Finset.sum_congr rfl (fun j _ => he j)
    _ = _ := by rw [Finset.sum_add_distrib]; simp [hmem]

end NLS.LpSequence
