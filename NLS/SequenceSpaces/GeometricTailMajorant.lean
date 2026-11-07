import NLS.SequenceSpaces.SummableGeometricTails

/-!
# Uniform Sobolev budgets from a common geometric-tail majorant

The full weighted sum, including the finite head, is bounded in terms of
the original unweighted sum and the sum of one common tail majorant. The
geometric cutoffs retain their boundary and the exact requested weight.
-/
noncomputable section
open scoped ENNReal
namespace NLS

private theorem sobolev_point_le_geometric_column
    (M : ℕ) (hM : 0 < M) (t : ℝ) (ht : 0 ≤ t) (n : ℤ) (a : ℝ) (ha : 0 ≤ a)
    (b : ℕ → ℝ) (hb : ∀ k, b k = ((4:ℝ)^t)^k*(if 4^k*M ≤ n.natAbs then a else 0))
    (hs : Summable b) :
    (1+|(n:ℝ)|)^t*a ≤ (1+4*(M:ℝ))^t*a+(1+4*(M:ℝ))^t*(∑' k, b k) := by
  let r := (4:ℝ)^t
  let D := (1+4*(M:ℝ))^t
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb0 (k : ℕ) : 0 ≤ b k := by rw [hb]; split_ifs <;> positivity
  have hsum : 0 ≤ ∑' k, b k := tsum_nonneg hb0
  by_cases hn : n.natAbs < M
  · have hbase : 1+|(n:ℝ)| ≤ 1+4*(M:ℝ) := by
      rw [show |(n:ℝ)| = (n.natAbs:ℝ) by simp only [Nat.cast_natAbs,Int.cast_abs]]
      have hnR : (n.natAbs:ℝ) < M := by exact_mod_cast hn
      have hMR : (0:ℝ) ≤ M := by positivity
      linarith
    have hweight := Real.rpow_le_rpow (by positivity) hbase ht
    exact (mul_le_mul_of_nonneg_right hweight (ha)).trans
      (le_add_of_nonneg_right (mul_nonneg hD hsum))
  · have hMR : (0:ℝ) < M := by exact_mod_cast hM
    have hnR : (M:ℝ) ≤ n.natAbs := by exact_mod_cast Nat.le_of_not_gt hn
    obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near (x := (n.natAbs:ℝ)/(M:ℝ))
      ((le_div_iff₀ hMR).mpr (by simpa using hnR)) (by norm_num : (1:ℝ)<4)
    have hcut : 4^k*M ≤ n.natAbs := by
      have h := (le_div_iff₀ hMR).mp hlo
      exact_mod_cast (show ((4^k*M:ℕ):ℝ) ≤ (n.natAbs:ℝ) by
        simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using h)
    have hbase : 1+|(n:ℝ)| ≤ (1+4*(M:ℝ))*(4:ℝ)^k := by
      have h := (div_lt_iff₀ hMR).mp hhi
      have hk : (1:ℝ) ≤ 4^k := one_le_pow₀ (by norm_num)
      rw [show |(n:ℝ)| = (n.natAbs:ℝ) by simp only [Nat.cast_natAbs,Int.cast_abs]]
      rw [pow_succ] at h
      nlinarith
    have hweight : (1+|(n:ℝ)|)^t ≤ D*r^k := by
      calc
        _ ≤ ((1+4*(M:ℝ))*(4:ℝ)^k)^t := Real.rpow_le_rpow (by positivity) hbase ht
        _ = D*r^k := by rw [Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_pow_comm (by norm_num)]
    have hterm : r^k*a ≤ ∑' j, b j := by
      have h := hs.le_tsum k (fun j _ => hb0 j)
      rw [hb k,if_pos hcut] at h
      exact h
    calc
      _ ≤ D*(r^k*a) := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hweight (ha)
      _ ≤ D*(∑' j, b j) := mul_le_mul_of_nonneg_left hterm hD
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg hD (ha))

/-- A summable upper bound on geometric tail energies gives an explicit
bound on the entire Sobolev sum, with the same weight and finite head. -/
theorem summable_sobolev_tsum_le_of_geometric_tail_majorant
    (f : ℤ → ℝ) (hf : ∀ n, 0 ≤ f n) (hs : Summable f)
    (M : ℕ) (hM : 0 < M) (t : ℝ) (ht : 0 ≤ t)
    (g : ℕ → ℝ) (hg : Summable g)
    (hb : ∀ k : ℕ, ((4:ℝ)^t)^k *
      (∑' n : ℤ, if 4^k*M ≤ n.natAbs then f n else 0) ≤ g k) :
    Summable (fun n : ℤ => (1+|(n:ℝ)|)^t*f n) ∧
      (∑' n : ℤ, (1+|(n:ℝ)|)^t*f n) ≤
        (1+4*(M:ℝ))^t*((∑' n, f n)+(∑' k, g k)) := by
  let r := (4:ℝ)^t
  let b (k : ℕ) (n : ℤ) := r^k*(if 4^k*M ≤ n.natAbs then f n else 0)
  have hr : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hb0 (k : ℕ) (n : ℤ) : 0 ≤ b k n := by
    dsimp only [b]
    split
    · exact mul_nonneg (pow_nonneg hr _) (hf n)
    · simp
  have htail (k : ℕ) : Summable (fun n : ℤ => if 4^k*M ≤ n.natAbs then f n else 0) :=
    hs.of_nonneg_of_le (fun n => by split; exact hf n; exact le_rfl)
      (fun n => by split <;> simp [hf])
  have hrow (k : ℕ) : Summable (b k) := (htail k).mul_left _
  have hrowbound (k : ℕ) : (∑' n, b k n) ≤ g k := by
    simpa only [b,r,tsum_mul_left] using hb k
  have hrows : Summable (fun k => ∑' n, b k n) :=
    hg.of_nonneg_of_le (fun k => tsum_nonneg (hb0 k)) hrowbound
  have hprod : Summable (fun kn : ℕ × ℤ => b kn.1 kn.2) :=
    (summable_prod_of_nonneg (fun kn => hb0 kn.1 kn.2)).mpr ⟨hrow,hrows⟩
  have hcols := (summable_prod_of_nonneg (fun nk : ℤ × ℕ => hb0 nk.2 nk.1)).mp hprod.prod_symm
  have hw : Summable (fun n : ℤ => (1+|(n:ℝ)|)^t*f n) :=
    summable_sobolev_of_summable_geometric_tails f hf hs M hM t ht
      (by simpa only [b,r,tsum_mul_left] using hrows)
  let D := (1+4*(M:ℝ))^t
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hpoint (n : ℤ) : (1+|(n:ℝ)|)^t*f n ≤ D*f n+D*(∑' k, b k n) :=
    sobolev_point_le_geometric_column M hM t ht n (f n) (hf n)
      (fun k => b k n) (fun _ => rfl) (hcols.1 n)
  refine ⟨hw,?_⟩
  have hsum := hw.tsum_le_tsum hpoint ((hs.mul_left D).add (hcols.2.mul_left D))
  have htotal : (∑' n : ℤ, ∑' k : ℕ, b k n) = (∑' k : ℕ, ∑' n : ℤ, b k n) :=
    Summable.tsum_comm (f := fun (k : ℕ) (n : ℤ) => b k n) hprod
  have he : (∑' n : ℤ, (D*f n+D*(∑' k : ℕ, b k n))) =
      D*((∑' n, f n)+(∑' k, ∑' n, b k n)) := by
    rw [Summable.tsum_add (hs.mul_left D) (hcols.2.mul_left D),tsum_mul_left,tsum_mul_left,
      htotal]
    ring
  exact hsum.trans (he.trans_le (mul_le_mul_of_nonneg_left
    (add_le_add le_rfl (hrows.tsum_le_tsum hrowbound hg)) hD))

end NLS
