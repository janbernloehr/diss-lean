import NLS.ZakharovShabat.SourceQuotientBlockRoots

/-!
# Quantitative lower bounds for the actual block quotient

On the L free centers beyond the block, each quotient error is at least
a/(6π). Consequently any l2 majorant has squared norm at least
L*(a/(6π))². These bounds concern the actual analytic product.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance sourceQuotientBlockLowerBoundFourFact : Fact (1 ≤ (4:ℝ≥0∞)) := ⟨by norm_num⟩

/-- A product of factors in `[0,1]` is bounded by the reciprocal of one plus their deficits. -/
theorem finite_prod_one_sub_le_reciprocal_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1) :
    (∏ i ∈ s, (1-x i)) ≤ 1/(1+∑ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hxa := hx a (by simp)
    have hxs := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hS : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg (fun i hi => (hxs i hi).1)
    rw [Finset.prod_insert ha,Finset.sum_insert ha]
    calc
      (1-x a)*(∏ i ∈ s, (1-x i)) ≤ (1-x a)*(1/(1+∑ i ∈ s, x i)) :=
        mul_le_mul_of_nonneg_left (ih hxs) (by linarith)
      _ = (1-x a)/(1+∑ i ∈ s, x i) := by ring
      _ ≤ 1/(1+(x a+∑ i ∈ s, x i)) := by
        apply (div_le_div_iff₀ (by linarith : 0 < 1+∑ i ∈ s, x i) (by linarith [hxa.1] : 0 < 1+(x a+∑ i ∈ s, x i))).mpr
        nlinarith [mul_nonneg hxa.1 hS,sq_nonneg (x a)]

/-- When the total deficit is at most one, half of it survives in the product deficit. -/
theorem half_sum_le_one_sub_finite_prod {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1) (hs : (∑ i ∈ s, x i) ≤ 1) :
    (∑ i ∈ s, x i)/2 ≤ 1-(∏ i ∈ s, (1-x i)) := by
  have hS : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg (fun i hi => (hx i hi).1)
  have hP := finite_prod_one_sub_le_reciprocal_sum s x hx
  have hr : 1/(1+∑ i ∈ s, x i) ≤ 1-(∑ i ∈ s, x i)/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_nonneg hS (sub_nonneg.mpr hs)]
  linarith

/-- Each of the next distant L centers gives a uniform positive quotient error. -/
theorem sourceSingleRootQuotient_block_error_lower (L : ℕ) (hL : 0 < L) (a : ℝ) (ha : 0 ≤ a) (haπ : a ≤ Real.pi)
    (n : ℤ) (hn : n ∈ Finset.Icc (2*(L:ℤ)+1) (3*(L:ℤ))) :
    a/(6*Real.pi) ≤ ‖sourceSingleRootQuotientJointProduct (p := 4) (by norm_num) (by norm_num) n
      ((Real.pi:ℂ)*n,(sourceQuotientBlock 4 L (a:ℂ),0))-1‖ := by
  let s := Finset.Icc (1:ℤ) L
  let x : ℤ → ℝ := fun m => a/(Real.pi*((n-m:ℤ):ℝ))
  have hLr : (0:ℝ) < L := by exact_mod_cast hL
  have hden (m : ℤ) (hm : m ∈ s) :
      (L:ℝ) ≤ ((n-m:ℤ):ℝ) ∧ ((n-m:ℤ):ℝ) ≤ 3*(L:ℝ) := by
    have hmi := Finset.mem_Icc.mp hm
    have hni := Finset.mem_Icc.mp hn
    constructor
    · exact_mod_cast (show (L:ℤ) ≤ n-m by omega)
    · exact_mod_cast (show n-m ≤ 3*(L:ℤ) by omega)
  have hx0 (m : ℤ) (hm : m ∈ s) : 0 ≤ x m :=
    div_nonneg ha (mul_nonneg Real.pi_pos.le (hLr.le.trans (hden m hm).1))
  have hxl (m : ℤ) (hm : m ∈ s) : a/(3*Real.pi*(L:ℝ)) ≤ x m := by
    dsimp [x]
    apply div_le_div_of_nonneg_left ha (mul_pos Real.pi_pos (hLr.trans_le (hden m hm).1))
    nlinarith [mul_le_mul_of_nonneg_left (hden m hm).2 Real.pi_pos.le]
  have hxu (m : ℤ) (hm : m ∈ s) : x m ≤ a/(Real.pi*(L:ℝ)) := by
    dsimp [x]
    exact div_le_div_of_nonneg_left ha (mul_pos Real.pi_pos hLr)
      (mul_le_mul_of_nonneg_left (hden m hm).1 Real.pi_pos.le)
  have hslo : a/(3*Real.pi) ≤ ∑ m ∈ s, x m := by
    have hb := Finset.sum_le_sum (fun m hm => hxl m hm)
    have hc : (∑ _m ∈ s, a/(3*Real.pi*(L:ℝ))) = a/(3*Real.pi) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      have hcard : s.card = L := by simp [s,Int.card_Icc]
      rw [hcard]
      field_simp
    rwa [hc] at hb
  have hshi : (∑ m ∈ s, x m) ≤ 1 := by
    have hb := Finset.sum_le_sum (fun m hm => hxu m hm)
    have hc : (∑ _m ∈ s, a/(Real.pi*(L:ℝ))) = a/Real.pi := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      have hcard : s.card = L := by simp [s,Int.card_Icc]
      rw [hcard]
      field_simp
    rw [hc] at hb
    exact hb.trans ((div_le_one Real.pi_pos).mpr haπ)
  have hprod := half_sum_le_one_sub_finite_prod s x
    (fun m hm => ⟨hx0 m hm,(Finset.single_le_sum hx0 hm).trans hshi⟩) hshi
  have hne : n ∉ Finset.Icc (1:ℤ) L := by
    have := Finset.mem_Icc.mp hn
    simp only [Finset.mem_Icc]
    omega
  have hQ := sourceSingleRootQuotient_block_eq_finiteProduct L a n hne
  have hreal : sourceSingleRootQuotientJointProduct (p := 4) (by norm_num) (by norm_num) n
      ((Real.pi:ℂ)*n,(sourceQuotientBlock 4 L (a:ℂ),0)) = ((∏ m ∈ s, (1-x m):ℝ):ℂ) := by
    rw [hQ]
    simp only [s,x,Complex.ofReal_prod,Complex.ofReal_sub,Complex.ofReal_one]
  rw [hreal,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have habs := neg_le_abs ((∏ m ∈ s, (1-x m))-1)
  have he : a/(6*Real.pi) = (a/(3*Real.pi))/2 := by ring
  rw [he]
  linarith

/-- Summing over those L centers forces this lower bound on every l2 majorant. -/
theorem sourceSingleRootQuotient_block_l2_lower (L : ℕ) (hL : 0 < L) (a : ℝ) (ha : 0 ≤ a) (haπ : a ≤ Real.pi)
    (B : Coeff 2)
    (hB : ∀ n ∈ Finset.Icc (2*(L:ℤ)+1) (3*(L:ℤ)),
      ‖sourceSingleRootQuotientJointProduct (p := 4) (by norm_num) (by norm_num) n
        ((Real.pi:ℂ)*n,(sourceQuotientBlock 4 L (a:ℂ),0))-1‖ ≤ ‖B n‖) :
    (L:ℝ)*(a/(6*Real.pi))^2 ≤ ‖B‖^2 := by
  let s := Finset.Icc (2*(L:ℤ)+1) (3*(L:ℤ))
  have hcard : s.card = L := by
    rw [Int.card_Icc]
    have he : 3*(L:ℤ)+1-(2*(L:ℤ)+1) = L := by ring
    rw [he]
    simp
  have hpoint (n : ℤ) (hn : n ∈ s) : (a/(6*Real.pi))^2 ≤ ‖B n‖^2 :=
    pow_le_pow_left₀ (by positivity) ((sourceSingleRootQuotient_block_error_lower L hL a ha haπ n hn).trans (hB n hn)) 2
  have hsum := Finset.sum_le_sum hpoint
  have hbound := lp.sum_rpow_le_norm_rpow (by norm_num : 0 < (2:ℝ≥0∞).toReal) B s
  have hbound' : (∑ n ∈ s, ‖B n‖^2) ≤ ‖B‖^2 := by simpa using! hbound
  have hfin : (L:ℝ)*(a/(6*Real.pi))^2 ≤ ∑ n ∈ s, ‖B n‖^2 := by
    simpa only [Finset.sum_const,nsmul_eq_mul,hcard] using hsum
  exact hfin.trans hbound'

end NLS.ZakharovShabat
