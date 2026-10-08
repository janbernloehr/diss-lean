import NLS.ZakharovShabat.FiniteGapPacking
import NLS.ZakharovShabat.GapRootFactorGeometry

/-! # Products over ordered real gaps outside their enclosing interval -/
noncomputable section
open scoped Classical
namespace NLS.ZakharovShabat

/-- The ratios for ordered disjoint intervals telescope to the enclosing ratio. -/
theorem prod_ordered_interval_ratios_le {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (l r : ι → ℝ) (a b x : ℝ) (hab : a ≤ b) (hx : b < x)
    (hb : ∀ i ∈ s, a ≤ l i ∧ l i ≤ r i ∧ r i ≤ b)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i < j → r i ≤ l j) :
    (∏ i ∈ s, (x-l i)/(x-r i)) ≤ (x-a)/(x-b) := by
  induction s using Finset.induction_on_min generalizing a with
  | empty => simp only [Finset.prod_empty]; apply (le_div_iff₀ (by linarith)).mpr; linarith
  | insert i s hi ih =>
    have hi' : i ∉ s := fun h => (lt_irrefl i) (hi i h)
    have hbi := hb i (Finset.mem_insert_self _ _)
    have hs := ih (r i) hbi.2.2
      (fun j hj => ⟨ho i (by simp) j (by simp [hj]) (hi j hj), (hb j (by simp [hj])).2⟩)
      (fun j hj k hk hjk => ho j (by simp [hj]) k (by simp [hk]) hjk)
    rw [Finset.prod_insert hi']
    calc
      _ ≤ ((x-l i)/(x-r i))*((x-r i)/(x-b)) :=
        mul_le_mul_of_nonneg_left hs (div_nonneg (by linarith) (by linarith))
      _ = (x-l i)/(x-b) := by
        have hd : x-r i ≠ 0 := ne_of_gt (by linarith)
        field_simp [hd]
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- The reflected ratio estimate for a point to the left of the intervals. -/
theorem prod_ordered_interval_ratios_left_le {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (l r : ι → ℝ) (a b x : ℝ) (hab : a ≤ b) (hx : x < a)
    (hb : ∀ i ∈ s, a ≤ l i ∧ l i ≤ r i ∧ r i ≤ b)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i < j → r i ≤ l j) :
    (∏ i ∈ s, (r i-x)/(l i-x)) ≤ (b-x)/(a-x) := by
  induction s using Finset.induction_on_max generalizing b with
  | empty => simp only [Finset.prod_empty]; apply (le_div_iff₀ (by linarith)).mpr; linarith
  | insert i s hi ih =>
    have hi' : i ∉ s := fun h => (lt_irrefl i) (hi i h)
    have hbi := hb i (Finset.mem_insert_self _ _)
    have hs := ih (l i) hbi.1
      (fun j hj => ⟨(hb j (by simp [hj])).1, (hb j (by simp [hj])).2.1,
        ho j (by simp [hj]) i (by simp) (hi j hj)⟩)
      (fun j hj k hk hjk => ho j (by simp [hj]) k (by simp [hk]) hjk)
    rw [Finset.prod_insert hi']
    calc
      _ ≤ ((r i-x)/(l i-x))*((l i-x)/(a-x)) :=
        mul_le_mul_of_nonneg_left hs (div_nonneg (by linarith) (by linarith))
      _ = (r i-x)/(a-x) := by
        have hd : l i-x ≠ 0 := ne_of_gt (by linarith)
        field_simp [hd]
      _ ≤ _ := div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- Squaring the factor norm exploits critical-point membership in the real gap. -/
theorem real_gap_root_factor_sq_le (l r c x : ℝ) (w : ℂ)
    (hlc : l ≤ c) (hcr : c ≤ r) (hx : r < x)
    (hw : w^2 = ((l:ℂ)-x)*((r:ℂ)-x)) :
    ‖((c:ℂ)-x)/w‖^2 ≤ (x-l)/(x-r) := by
  have hnorm : ‖w‖^2 = (x-l)*(x-r) := by
    have h := congrArg norm hw
    rw [norm_pow,norm_mul,← Complex.ofReal_sub,← Complex.ofReal_sub,
      Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_neg (by linarith : l-x < 0),abs_of_neg (by linarith : r-x < 0)] at h
    nlinarith
  have hnum : ‖(c:ℂ)-x‖ = x-c := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_neg (by linarith : c-x < 0)]
    ring
  rw [norm_div,div_pow,hnorm,hnum]
  calc
    _ ≤ (x-l)^2/((x-l)*(x-r)) :=
      div_le_div_of_nonneg_right (by nlinarith) (mul_nonneg (by linarith) (by linarith))
    _ = (x-l)/(x-r) := by field_simp

/-- The same squared-factor estimate on the left of the real gap. -/
theorem real_gap_root_factor_sq_left_le (l r c x : ℝ) (w : ℂ)
    (hlc : l ≤ c) (hcr : c ≤ r) (hx : x < l)
    (hw : w^2 = ((l:ℂ)-x)*((r:ℂ)-x)) :
    ‖((c:ℂ)-x)/w‖^2 ≤ (r-x)/(l-x) := by
  have h := real_gap_root_factor_sq_le (-r) (-l) (-c) (-x) w
    (by linarith) (by linarith) (by linarith) (by rw [hw]; push_cast; ring)
  have he : ((-c:ℝ):ℂ)-((-x:ℝ):ℂ) = -((c:ℂ)-x) := by push_cast; ring
  simpa only [he,neg_div,norm_neg,neg_sub_neg] using h

/-- The squared norm of the entire ordered-gap product has a single enclosing ratio.
This covers both sides of the real spectrum and collapsed intervals. -/
theorem ordered_real_gap_product_sq_le {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (l r c : ι → ℝ) (w : ι → ℂ) (A x : ℝ)
    (hA : 0 ≤ A) (hx : A < |x|)
    (hb : ∀ i ∈ s, -A ≤ l i ∧ l i ≤ c i ∧ c i ≤ r i ∧ r i ≤ A)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i < j → r i ≤ l j)
    (hw : ∀ i ∈ s, (w i)^2 = ((l i:ℂ)-x)*((r i:ℂ)-x)) :
    ‖∏ i ∈ s, ((c i:ℂ)-x)/w i‖^2 ≤ (|x|+A)/(|x|-A) := by
  rw [norm_prod,← Finset.prod_pow]
  by_cases hx0 : 0 ≤ x
  · rw [abs_of_nonneg hx0] at hx ⊢
    have hp : (∏ i ∈ s, ‖((c i:ℂ)-x)/w i‖^2) ≤ ∏ i ∈ s, (x-l i)/(x-r i) := by
      apply Finset.prod_le_prod (fun i _ => sq_nonneg _)
      intro i hi
      have hi' := hb i hi
      exact real_gap_root_factor_sq_le _ _ _ _ _ hi'.2.1 hi'.2.2.1
        (lt_of_le_of_lt hi'.2.2.2 hx) (hw i hi)
    have h := prod_ordered_interval_ratios_le s l r (-A) A x (by linarith) hx
      (fun i hi => ⟨(hb i hi).1,le_trans (hb i hi).2.1 (hb i hi).2.2.1,(hb i hi).2.2.2⟩) ho
    exact hp.trans (by simpa only [sub_neg_eq_add] using h)
  · rw [abs_of_neg (lt_of_not_ge hx0)] at hx ⊢
    have hp : (∏ i ∈ s, ‖((c i:ℂ)-x)/w i‖^2) ≤ ∏ i ∈ s, (r i-x)/(l i-x) := by
      apply Finset.prod_le_prod (fun i _ => sq_nonneg _)
      intro i hi
      have hi' := hb i hi
      exact real_gap_root_factor_sq_left_le _ _ _ _ _ hi'.2.1 hi'.2.2.1 (by linarith [hi'.1]) (hw i hi)
    have h := prod_ordered_interval_ratios_left_le s l r (-A) A x (by linarith) (by linarith)
      (fun i hi => ⟨(hb i hi).1,le_trans (hb i hi).2.1 (hb i hi).2.2.1,(hb i hi).2.2.2⟩) ho
    have he : (A-x)/(-A-x) = (-x+A)/(-x-A) := by congr 1 <;> ring
    exact hp.trans (h.trans_eq he)

end NLS.ZakharovShabat
