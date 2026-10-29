import NLS.ZakharovShabat.SourceQuotientAsymptoticGeometry

/-!
# Literal scalar and near/far bounds in Lemma 10.8

The inverse-square-root estimate retains the printed constant one on the
closed half-unit ball. The near/far estimates use the lp norm of the gap
sequence, and the near term keeps the factor one quarter. The original
isolating disks retain their supplied separation constant.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The printed constant one holds throughout the closed half-unit ball. -/
theorem norm_inv_sqrt_one_sub_sub_one_le_one (q : ℂ) (hq : ‖q‖ ≤ 1/2) :
    ‖(Complex.sqrt (1-q))⁻¹-1‖ ≤ ‖q‖ := by
  let s := Complex.sqrt (1-q)
  have hs : s^2 = 1-q := by
    dsimp [s]
    have h := Complex.cpow_nat_inv_pow (1-q) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt, one_div] using h
  have hre : 0 ≤ s.re := by
    dsimp [s]
    rw [Complex.sqrt, Complex.cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hsre := congrArg Complex.re hs
  simp only [pow_two, Complex.mul_re, Complex.sub_re, Complex.one_re] at hsre
  have hqr : q.re ≤ 1/2 := (Complex.re_le_norm q).trans hq
  have hrelow : (2/3 : ℝ) ≤ s.re := by nlinarith [sq_nonneg s.im]
  have hsn : (2/3 : ℝ) ≤ ‖s‖ := hrelow.trans (Complex.re_le_norm s)
  have hplus : (5/3 : ℝ) ≤ ‖s+1‖ := by
    have h := Complex.re_le_norm (s+1)
    simp only [Complex.add_re, Complex.one_re] at h
    linarith
  have hden : 1 ≤ ‖s*(s+1)‖ := by
    rw [norm_mul]
    nlinarith
  have hs0 : s ≠ 0 := by
    intro h
    norm_num [h] at hsn
  have hplus0 : s+1 ≠ 0 := by
    intro h
    norm_num [h] at hplus
  have heq : s⁻¹-1 = q/(s*(s+1)) := by
    apply (eq_div_iff (mul_ne_zero hs0 hplus0)).2
    calc
      (s⁻¹-1)*(s*(s+1)) = 1-s^2 := by field_simp; ring
      _ = q := by rw [hs]; ring
  change ‖s⁻¹-1‖ ≤ ‖q‖
  rw [heq, norm_div]
  exact div_le_self (norm_nonneg _) hden

/-- The literal constant one also removes the factor two in the product exponential. -/
theorem norm_prod_inv_sqrt_one_sub_sub_one_le_sum
    {ι : Type*} (s : Finset ι) (q : ι → ℂ)
    (hq : ∀ i ∈ s, ‖q i‖ ≤ 1/2) :
    ‖(∏ i ∈ s, (Complex.sqrt (1-q i))⁻¹)-1‖ ≤
      Real.exp (∑ i ∈ s, ‖q i‖)-1 := by
  let u : ι → ℂ := fun i => (Complex.sqrt (1-q i))⁻¹-1
  have hsum : (∑ i ∈ s, ‖u i‖) ≤ ∑ i ∈ s, ‖q i‖ :=
    Finset.sum_le_sum (fun i hi => norm_inv_sqrt_one_sub_sub_one_le_one (q i) (hq i hi))
  have heq : (∏ i ∈ s, (1+u i)) =
      ∏ i ∈ s, (Complex.sqrt (1-q i))⁻¹ := by
    apply Finset.prod_congr rfl
    intro i _
    dsimp [u]
    ring
  rw [← heq]
  exact (s.norm_prod_one_add_sub_one_le u).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Far differences are controlled by the original lp norm of the unsquared gap. -/
theorem gapCoefficient_far_bound (g : Coeff p) (C : ℝ) (m n : ℤ)
    (hn : n ≠ 0) (hfar : |(n : ℝ)|/2 ≤ |((m-n : ℤ) : ℝ)|) :
    C^2*‖g m‖^2/(4*|((m-n : ℤ) : ℝ)|^2) ≤ C^2*‖g‖^2/|(n : ℝ)|^2 := by
  have hnR : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
  have hd : 0 < |((m-n : ℤ) : ℝ)| := by linarith
  have hg := lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' g m
  have hgsq : ‖g m‖^2 ≤ ‖g‖^2 := pow_le_pow_left₀ (norm_nonneg _) hg 2
  have hden : |(n : ℝ)|^2 ≤ 4*|((m-n : ℤ) : ℝ)|^2 := by nlinarith
  calc
    _ ≤ C^2*‖g‖^2/(4*|((m-n : ℤ) : ℝ)|^2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hgsq (sq_nonneg C)) (by positivity)
    _ ≤ C^2*‖g‖^2/|(n : ℝ)|^2 :=
      div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hnR) hden

/-- Near differences see only the lp tail beyond half the omitted index. -/
theorem gapCoefficient_near_bound (g : Coeff p) (C : ℝ) (m n : ℤ)
    (hmn : m ≠ n) (hnear : |((m-n : ℤ) : ℝ)| < |(n : ℝ)|/2) :
    C^2*‖g m‖^2/(4*|((m-n : ℤ) : ℝ)|^2) ≤
      (C^2/4)*‖g-Coeff.truncate
        (Finset.Icc (-((n.natAbs/2 : ℕ) : ℤ)) ((n.natAbs/2 : ℕ) : ℤ)) g‖^2 := by
  have htriangle : n.natAbs ≤ m.natAbs+(m-n).natAbs := by
    have h := Int.natAbs_add_le m (n-m)
    rw [show n-m = -(m-n) by ring, Int.natAbs_neg] at h
    rw [show m + -(m-n) = n by ring] at h
    exact h
  have hnearN : 2*(m-n).natAbs < n.natAbs := by
    have he (a : ℤ) : |(a : ℝ)| = (a.natAbs : ℝ) := by simp
    rw [he, he] at hnear
    exact_mod_cast (show 2*((m-n).natAbs : ℝ) < (n.natAbs : ℝ) by linarith)
  have hm : n.natAbs/2 < m.natAbs := by omega
  let F := Finset.Icc (-((n.natAbs/2 : ℕ) : ℤ)) ((n.natAbs/2 : ℕ) : ℤ)
  have hmF : m ∉ F := by
    simp only [F, Finset.mem_Icc]
    omega
  have hg := lp.norm_apply_le_norm (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
    (g-Coeff.truncate F g) m
  have hcoord : ‖g m‖ ≤ ‖g-Coeff.truncate F g‖ := by
    simpa only [lp.coeFn_sub, Pi.sub_apply, Coeff.truncate_apply, if_neg hmF, sub_zero] using hg
  have hdN : 1 ≤ (m-n).natAbs := by omega
  have hd : 1 ≤ |((m-n : ℤ) : ℝ)| := by
    have habs : |((m-n : ℤ) : ℝ)| = ((m-n).natAbs : ℝ) := by simp
    rw [habs]
    exact_mod_cast hdN
  have hgsq := pow_le_pow_left₀ (norm_nonneg _) hcoord 2
  change _ ≤ (C^2/4)*‖g-Coeff.truncate F g‖^2
  have hden : 4 ≤ 4*|((m-n : ℤ) : ℝ)|^2 := by nlinarith
  calc
    _ ≤ C^2*‖g m‖^2/4 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
    _ ≤ (C^2/4)*‖g-Coeff.truncate F g‖^2 := by nlinarith [mul_le_mul_of_nonneg_left hgsq (sq_nonneg C)]

/-- Every original disk satisfies the displayed quarter-gap bound with the same constant. -/
theorem SourceIsolatingNeighborhoods.gapRadicand_le_index
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n m : ℤ) (hmn : m ≠ n)
    (z : ℂ) (hz : z ∈ D n) :
    ‖sourceSingleRootGapRadicand hp hp1 ψ m z‖ ≤
      c^2*‖sourcePeriodicGapDisplacement hp hp1 ψ m‖^2/
        (4*|((m-n : ℤ) : ℝ)|^2) := by
  let d : ℝ := |((m-n : ℤ) : ℝ)|
  let b : ℝ := ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) m-z‖
  let g : ℝ := ‖sourcePeriodicGapDisplacement hp hp1 ψ m‖
  have hd : 0 < d := abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr hmn)
  have hc : 0 < c := zero_lt_one.trans_le hD.one_le
  have hsep : d ≤ c*b := by
    have hh := hD.midpoint_separation ψ hψ n m hmn.symm z hz
    simpa only [d,b,show n-m = -(m-n) by ring,Int.cast_neg,abs_neg] using hh
  have hb : 0 < b := by
    have hb0 : 0 ≤ b := norm_nonneg _
    nlinarith
  have hden : d^2 ≤ c^2*b^2 := by
    have hh := pow_le_pow_left₀ hd.le hsep 2
    nlinarith
  have hnorm : ‖sourceSingleRootGapRadicand hp hp1 ψ m z‖ = g^2/(4*b^2) := by
    simp only [sourceSingleRootGapRadicand,norm_div,norm_pow,norm_mul,norm_ofNat,
      ← sourcePeriodicGapDisplacement_apply,g,b]
  rw [hnorm]
  change g^2/(4*b^2) ≤ c^2*g^2/(4*d^2)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [mul_le_mul_of_nonneg_left hden (sq_nonneg g)]

end NLS.ZakharovShabat
