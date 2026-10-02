import NLS.SequenceSpaces.FourierTail
import NLS.SequenceSpaces.Weighted
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Weighted summability from geometric Fourier tails

Sum the tails over geometric cutoffs before estimating individual
coefficients. This retains the full regularity gain of the tail bound.
-/

noncomputable section
open scoped ENNReal
namespace NLS

/-- A geometric bound on tail sums gives weighted summability whenever
weight growth times tail decay is strictly contracting. -/
theorem summable_sobolev_of_geometric_tail
    (f : ℤ → ℝ) (hf : ∀ n, 0 ≤ f n) (hs : Summable f)
    (M : ℕ) (hM : 0 < M) (C q t : ℝ) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hrq : (4 : ℝ)^t*q < 1)
    (hb : ∀ k : ℕ, (∑' n : ℤ, if 4^k*M ≤ n.natAbs then f n else 0) ≤ C*q^k) :
    Summable (fun n : ℤ => (1+|(n : ℝ)|)^t*f n) := by
  let r := (4 : ℝ)^t
  let b (k : ℕ) (n : ℤ) := r^k * (if 4^k*M ≤ n.natAbs then f n else 0)
  have hr : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hb0 (k : ℕ) (n : ℤ) : 0 ≤ b k n := by
    dsimp only [b]; split
    · exact mul_nonneg (pow_nonneg hr _) (hf _)
    · simp
  have htail (k : ℕ) : Summable (fun n : ℤ => if 4^k*M ≤ n.natAbs then f n else 0) :=
    hs.of_nonneg_of_le (fun n => by split; exact hf n; exact le_rfl)
      (fun n => by split <;> simp [hf])
  have hrow (k : ℕ) : Summable (b k) := (htail k).mul_left _
  have hrows : Summable (fun k => ∑' n, b k n) := by
    apply ((summable_geometric_of_lt_one (mul_nonneg hr hq) hrq).mul_left C).of_nonneg_of_le
      (fun k => tsum_nonneg (hb0 k))
    intro k
    dsimp only [b]
    rw [tsum_mul_left, mul_pow]
    have h := mul_le_mul_of_nonneg_left (hb k) (pow_nonneg hr k)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  have hprod : Summable (fun kn : ℕ × ℤ => b kn.1 kn.2) :=
    (summable_prod_of_nonneg (fun kn => hb0 kn.1 kn.2)).mpr ⟨hrow,hrows⟩
  have hcols := (summable_prod_of_nonneg (fun nk : ℤ × ℕ => hb0 nk.2 nk.1)).mp
    hprod.prod_symm
  let D := (1+4*(M : ℝ))^t
  have hD : 0 ≤ D := by dsimp [D]; positivity
  apply ((hs.mul_left D).add (hcols.2.mul_left D)).of_nonneg_of_le
    (fun n => mul_nonneg (Real.rpow_nonneg (by positivity) _) (hf n))
  intro n
  have hsum : 0 ≤ ∑' k, b k n := tsum_nonneg (fun k => hb0 k n)
  by_cases hn : n.natAbs < M
  · have hbase : 1+|(n : ℝ)| ≤ 1+4*(M : ℝ) := by
      rw [show |(n : ℝ)| = (n.natAbs : ℝ) by simp only [Nat.cast_natAbs, Int.cast_abs]]
      have hnR : (n.natAbs : ℝ) < M := by exact_mod_cast hn
      have hMR : (0 : ℝ) ≤ M := by positivity
      linarith
    have hweight := Real.rpow_le_rpow (by positivity) hbase ht
    have h := mul_le_mul_of_nonneg_right hweight (hf n)
    exact h.trans (le_add_of_nonneg_right (mul_nonneg hD hsum))
  · have hMR : (0 : ℝ) < M := by exact_mod_cast hM
    have hnR : (M : ℝ) ≤ n.natAbs := by exact_mod_cast (Nat.le_of_not_gt hn)
    obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near (x := (n.natAbs : ℝ)/(M : ℝ))
      ((le_div_iff₀ hMR).mpr (by simpa using hnR)) (by norm_num : (1 : ℝ) < 4)
    have hcut : 4^k*M ≤ n.natAbs := by
      have h := (le_div_iff₀ hMR).mp hlo
      exact_mod_cast (show ((4^k*M : ℕ) : ℝ) ≤ (n.natAbs : ℝ) by
        simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h)
    have hbase : 1+|(n : ℝ)| ≤ (1+4*(M : ℝ))*(4 : ℝ)^k := by
      have h := (div_lt_iff₀ hMR).mp hhi
      have hk : (1 : ℝ) ≤ 4^k := one_le_pow₀ (by norm_num)
      rw [show |(n : ℝ)| = (n.natAbs : ℝ) by simp only [Nat.cast_natAbs, Int.cast_abs]]
      rw [pow_succ] at h
      nlinarith
    have hweight : (1+|(n : ℝ)|)^t ≤ D*r^k := by
      calc
        _ ≤ ((1+4*(M : ℝ))*(4 : ℝ)^k)^t := Real.rpow_le_rpow (by positivity) hbase ht
        _ = D*r^k := by rw [Real.mul_rpow (by positivity) (by positivity),
          ← Real.rpow_pow_comm (by norm_num)]
    have hterm : r^k*f n ≤ ∑' j, b j n := by
      simpa only [b,if_pos hcut] using (hcols.1 n).le_tsum k (fun j _ => hb0 j n)
    calc
      _ ≤ D*(r^k*f n) := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hweight (hf n)
      _ ≤ D*(∑' j, b j n) := mul_le_mul_of_nonneg_left hterm hD
      _ ≤ D*f n+D*(∑' j, b j n) := le_add_of_nonneg_left (mul_nonneg hD (hf n))

namespace Coeff

/-- Geometric decay of the `p`th power of the Fourier-tail norm
implies membership in the Sobolev-weighted coefficient space. -/
theorem mem_sobolev_of_geometric_tail
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 0 < p.toReal) (a : Coeff p)
    (M : ℕ) (hM : 0 < M) (C q s : ℝ) (hq : 0 ≤ q) (hs : 0 ≤ s)
    (hrq : (4 : ℝ)^(s*p.toReal)*q < 1)
    (hb : ∀ k : ℕ, ‖fourierTail (4^k*M) a‖^p.toReal ≤ C*q^k) :
    Memℓp (fun n => (Weight.sobolev s n : ℂ)*a n) p := by
  have hsum := summable_sobolev_of_geometric_tail (fun n => ‖a n‖^p.toReal)
    (fun n => Real.rpow_nonneg (norm_nonneg _) _) (a.property.summable hp)
    M hM C q (s*p.toReal) hq (mul_nonneg hs hp.le) hrq (fun k => by
      convert hb k using 1
      rw [lp.norm_rpow_eq_tsum hp]
      apply tsum_congr
      intro n
      rw [fourierTail_apply]
      split <;> simp [Real.zero_rpow (ne_of_gt hp)])
  apply memℓp_gen
  convert hsum using 1
  funext n
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ((Weight.sobolev s).positive n), Weight.sobolev_apply,
    Real.mul_rpow (by positivity) (norm_nonneg _), ← Real.rpow_mul (by positivity)]

end Coeff
end NLS
