import NLS.SequenceSpaces.GeometricTailRegularity

/-! # Exact Sobolev regularity from summable geometric tails

For positive orders, weighted coefficient summability is equivalent to
summability of four-adic tails at the exact same weight. Tonelli retains
the full regularity order, including the finite central block.
-/

noncomputable section
open scoped ENNReal
namespace NLS
/-- Summable geometrically weighted tails give the exact Sobolev coefficient weight.
The zero-order case is included in this direction. -/
theorem summable_sobolev_of_summable_geometric_tails
    (f : ℤ → ℝ) (hf : ∀ n, 0 ≤ f n) (hs : Summable f)
    (M : ℕ) (hM : 0 < M) (t : ℝ) (ht : 0 ≤ t)
    (hb : Summable (fun k : ℕ => ((4:ℝ)^t)^k * (∑' n : ℤ, if 4^k*M ≤ n.natAbs then f n else 0))) :
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
    simpa only [b,tsum_mul_left] using hb
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

/-- A positive Sobolev coefficient weight makes the tails summable at exactly
that geometric rate. Positivity of the order is essential in this direction. -/
theorem summable_geometric_tails_of_summable_sobolev
    (f : ℤ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (M : ℕ) (hM : 0 < M) (t : ℝ) (ht : 0 < t)
    (hw : Summable (fun n : ℤ => (1+|(n:ℝ)|)^t*f n)) :
    Summable (fun k : ℕ => ((4:ℝ)^t)^k * (∑' n : ℤ, if 4^k*M ≤ n.natAbs then f n else 0)) := by
  let r := (4:ℝ)^t
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) ht
  let b := fun (k : ℕ) (n : ℤ) => r^k*(if 4^k*M ≤ n.natAbs then f n else 0)
  have hb0 (k : ℕ) (n : ℤ) : 0 ≤ b k n := by
    dsimp [b]
    split_ifs
    · exact mul_nonneg (pow_nonneg (zero_lt_one.trans hr).le _) (hf _)
    · simp
  have hcol (n : ℤ) : Summable (fun k => b k n) ∧
      (∑' k, b k n) ≤ (r/(r-1))*((1+|(n:ℝ)|)^t*f n) := by
    obtain ⟨K,hlo,hhi⟩ := exists_nat_pow_near
      (x := 1+|(n:ℝ)|) (by linarith [abs_nonneg (n:ℝ)]) (by norm_num : (1:ℝ)<4)
    have hsupp (k : ℕ) (hk : k ∉ Finset.range (K+1)) : b k n = 0 := by
      have hkK : K+1 ≤ k := by simpa only [Finset.mem_range,not_lt] using hk
      have hnot : ¬4^k*M ≤ n.natAbs := by
        intro hcut
        have hpow : (4:ℕ)^k ≤ n.natAbs := (Nat.le_mul_of_pos_right _ hM).trans hcut
        have hpowR : (4:ℝ)^k ≤ |(n:ℝ)| := by
          have h : ((4:ℕ)^k:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast hpow
          simpa only [Nat.cast_pow,Nat.cast_ofNat,Nat.cast_natAbs,Int.cast_abs] using h
        have hpowK : (4:ℝ)^(K+1) ≤ (4:ℝ)^k := pow_le_pow_right₀ (by norm_num) hkK
        linarith
      simp only [b,if_neg hnot,mul_zero]
    have hsum : Summable (fun k => b k n) := summable_of_ne_finset_zero hsupp
    refine ⟨hsum,?_⟩
    rw [tsum_eq_sum hsupp]
    have hgeo : (∑ k ∈ Finset.range (K+1), r^k) ≤ (r/(r-1))*(1+|(n:ℝ)|)^t := by
      rw [geom_sum_eq hr.ne' (K+1)]
      apply (div_le_iff₀ (sub_pos.mpr hr)).mpr
      have hpow : r^K ≤ (1+|(n:ℝ)|)^t := by
        dsimp only [r]
        rw [Real.rpow_pow_comm (by norm_num)]
        exact Real.rpow_le_rpow (by positivity) hlo ht.le
      have hmul := mul_le_mul_of_nonneg_left hpow (zero_lt_one.trans hr).le
      have he : r/(r-1)*(1+|(n:ℝ)|)^t*(r-1) = r*(1+|(n:ℝ)|)^t := by
        field_simp [sub_ne_zero.mpr hr.ne']
      rw [he,pow_succ]
      nlinarith
    calc
      _ ≤ ∑ k ∈ Finset.range (K+1), r^k*f n := Finset.sum_le_sum (fun k _ => by
        dsimp [b]
        split_ifs
        · exact le_rfl
        · simp only [mul_zero]; exact mul_nonneg (pow_nonneg (zero_lt_one.trans hr).le _) (hf n))
      _ = (∑ k ∈ Finset.range (K+1), r^k)*f n := (Finset.sum_mul _ _ _).symm
      _ ≤ ((r/(r-1))*(1+|(n:ℝ)|)^t)*f n := mul_le_mul_of_nonneg_right hgeo (hf n)
      _ = _ := by ring
  have hcols : Summable (fun n => ∑' k, b k n) :=
    (hw.mul_left (r/(r-1))).of_nonneg_of_le (fun n => tsum_nonneg (fun k => hb0 k n))
      (fun n => (hcol n).2)
  have hprod : Summable (fun nk : ℤ × ℕ => b nk.2 nk.1) :=
    (summable_prod_of_nonneg (fun nk => hb0 nk.2 nk.1)).mpr ⟨fun n => (hcol n).1,hcols⟩
  have hrows := ((summable_prod_of_nonneg (fun kn : ℕ × ℤ => hb0 kn.1 kn.2)).mp hprod.prod_symm).2
  simpa only [b,tsum_mul_left] using hrows

namespace Coeff

/-- Exact Sobolev membership from summability of weighted Fourier-tail energies. -/
theorem mem_sobolev_of_summable_geometric_tails
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 0 < p.toReal) (a : Coeff p)
    (M : ℕ) (hM : 0 < M) (s : ℝ) (hs : 0 ≤ s)
    (hb : Summable (fun k : ℕ => ((4:ℝ)^(s*p.toReal))^k*‖fourierTail (4^k*M) a‖^p.toReal)) :
    Memℓp (fun n => (Weight.sobolev s n:ℂ)*a n) p := by
  have hsum := summable_sobolev_of_summable_geometric_tails (fun n => ‖a n‖^p.toReal)
    (fun n => Real.rpow_nonneg (norm_nonneg _) _) (a.property.summable hp)
    M hM (s*p.toReal) (mul_nonneg hs hp.le) (by
      convert hb using 1
      funext k
      rw [lp.norm_rpow_eq_tsum hp]
      congr 1
      apply tsum_congr
      intro n
      rw [fourierTail_apply]
      split <;> simp [Real.zero_rpow hp.ne'])
  apply memℓp_gen
  convert hsum using 1
  funext n
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos ((Weight.sobolev s).positive n),Weight.sobolev_apply,
    Real.mul_rpow (by positivity) (norm_nonneg _),← Real.rpow_mul (by positivity)]
end Coeff

end NLS
