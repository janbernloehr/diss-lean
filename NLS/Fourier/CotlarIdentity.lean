import NLS.Fourier.DiscreteHilbert

/-!
# The discrete Cotlar identity

Partial fractions cancel the off-diagonal terms in the square of the ordinary
Hilbert transform. The remaining diagonal terms have an absolutely summable
square kernel. This is the algebraic step for doubling strong exponents.
-/

noncomputable section
open Complex
namespace NLS.Fourier

/-- The scalar partial-fraction identity, including all collisions of indices. -/
theorem cotlar_kernel (x y z : ℂ) :
    (x - z)⁻¹ * (y - z)⁻¹ =
      (x - z)⁻¹ * (y - x)⁻¹ + (y - z)⁻¹ * (x - y)⁻¹ +
      (if x = y then ((x - z)⁻¹)^2 else 0) +
      (if y = z then ((x - z)⁻¹)^2 else 0) +
      (if x = z then ((y - z)⁻¹)^2 else 0) := by
  classical
  by_cases hx : x = z
  · subst x
    by_cases hy : y = z
    · subst y
      simp
    · simp only [if_neg hy, if_neg (Ne.symm hy), ite_true, sub_self, inv_zero,
        zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, zero_add]
      rw [show z - y = -(y - z) by ring, inv_neg]
      ring
  · by_cases hy : y = z
    · subst y
      simp only [if_neg hx, ite_true, sub_self, inv_zero, mul_zero, add_zero]
      rw [show z - x = -(x - z) by ring, inv_neg]
      ring
    · by_cases hxy : x = y
      · subst y
        simp [hx, pow_two]
      · simp only [if_neg hx, if_neg hy, if_neg hxy, add_zero]
        have hx' := sub_ne_zero.mpr hx
        have hy' := sub_ne_zero.mpr hy
        have hxy' := sub_ne_zero.mpr hxy
        have hyx' := sub_ne_zero.mpr (Ne.symm hxy)
        field_simp
        ring

/-- Pointwise multiplication retaining the finite support of the first factor. -/
def finiteProduct (a : ℤ →₀ ℂ) (f : ℤ → ℂ) : ℤ →₀ ℂ :=
  Finsupp.onFinset a.support (fun n => a n * f n) (by
    intro n hn
    exact Finsupp.mem_support_iff.mpr (fun h => hn (by simp [h])))

@[simp] theorem finiteProduct_apply (a : ℤ →₀ ℂ) (f : ℤ → ℂ) (n : ℤ) :
    finiteProduct a f n = a n * f n := rfl

/-- The square-kernel remainder on finite input. -/
def finiteHilbertSquare (a : ℤ →₀ ℂ) (n : ℤ) : ℂ :=
  a.sum (fun k z => z / (((k : ℂ) - n)^2))

private theorem cotlar_weighted (a : ℤ → ℂ) (j k n : ℤ) :
    (a j * ((j : ℂ) - n)⁻¹) * (a k * ((k : ℂ) - n)⁻¹) =
      (a j * ((j : ℂ) - n)⁻¹) * (a k * ((k : ℂ) - j)⁻¹) +
      (a k * ((k : ℂ) - n)⁻¹) * (a j * ((j : ℂ) - k)⁻¹) +
      (if j = k then (a j)^2 * (((j : ℂ) - n)⁻¹)^2 else 0) +
      (if k = n then a j * a n * (((j : ℂ) - n)⁻¹)^2 else 0) +
      (if j = n then a n * a k * (((k : ℂ) - n)⁻¹)^2 else 0) := by
  have h := congrArg (fun z : ℂ => a j * a k * z) (cotlar_kernel (j : ℂ) (k : ℂ) (n : ℂ))
  simp only [Int.cast_inj] at h
  split_ifs at h ⊢ <;> subst_vars <;> linear_combination h

/-- The finite-sum Cotlar identity, including its two discrete correction terms. -/
theorem cotlar_sum (s : Finset ℤ) (a : ℤ → ℂ) (n : ℤ) (hn : n ∈ s) :
    (∑ j ∈ s, a j * ((j : ℂ) - n)⁻¹)^2 =
      2 * (∑ j ∈ s, (a j * ((j : ℂ) - n)⁻¹) * (∑ k ∈ s, a k * ((k : ℂ) - j)⁻¹)) +
      (∑ j ∈ s, (a j)^2 * (((j : ℂ) - n)⁻¹)^2) +
      2 * a n * (∑ j ∈ s, a j * (((j : ℂ) - n)⁻¹)^2) := by
  have h := Finset.sum_congr (s₁ := s) rfl (fun j hj =>
    Finset.sum_congr (s₁ := s) rfl (fun k hk => cotlar_weighted a j k n))
  simp only [Finset.sum_add_distrib] at h
  have hdiag : (∑ j ∈ s, ∑ k ∈ s, if j = k then (a j)^2 * (((j : ℂ) - n)⁻¹)^2 else 0) =
      ∑ j ∈ s, (a j)^2 * (((j : ℂ) - n)⁻¹)^2 := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [hj]
  have hsym : (∑ j ∈ s, ∑ k ∈ s,
      (a k * ((k : ℂ) - n)⁻¹) * (a j * ((j : ℂ) - k)⁻¹)) =
      ∑ j ∈ s, ∑ k ∈ s, (a j * ((j : ℂ) - n)⁻¹) * (a k * ((k : ℂ) - j)⁻¹) :=
    Finset.sum_comm
  rw [hdiag, hsym] at h
  simp only [Finset.sum_ite_eq', if_pos hn, Finset.sum_ite_irrel, Finset.sum_const_zero] at h
  simp only [← Finset.mul_sum, ← Finset.sum_mul] at h
  have hr : (∑ j ∈ s, a j * a n * (((j : ℂ) - n)⁻¹)^2) =
      a n * ∑ j ∈ s, a j * (((j : ℂ) - n)⁻¹)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hr] at h
  have hr2 : (∑ j ∈ s, a n * a j * (((j : ℂ) - n)⁻¹)^2) =
      a n * ∑ j ∈ s, a j * (((j : ℂ) - n)⁻¹)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hr2] at h
  linear_combination h

theorem support_finiteProduct_subset (a : ℤ →₀ ℂ) (f : ℤ → ℂ) :
    (finiteProduct a f).support ⊆ a.support := Finsupp.support_onFinset_subset

/-- The ordinary transform satisfies the discrete Cotlar identity on every finite input. -/
theorem finiteHilbert_cotlar (a : ℤ →₀ ℂ) (n : ℤ) :
    (finiteHilbert a n)^2 = 2 * finiteHilbert (finiteProduct a (finiteHilbert a)) n +
      finiteHilbertSquare (finiteProduct a a) n + 2 * a n * finiteHilbertSquare a n := by
  let s := insert n a.support
  have ha : a.support ⊆ s := Finset.subset_insert _ _
  have hn : n ∈ s := Finset.mem_insert_self _ _
  have hH (j : ℤ) : finiteHilbert a j = ∑ k ∈ s, a k * ((k : ℂ) - j)⁻¹ := by
    unfold finiteHilbert
    rw [Finsupp.sum_of_support_subset a ha _ (by simp)]
    simp only [div_eq_mul_inv]
  have hP (f : ℤ → ℂ) : finiteHilbert (finiteProduct a f) n =
      ∑ j ∈ s, (a j * f j) * ((j : ℂ) - n)⁻¹ := by
    unfold finiteHilbert
    rw [Finsupp.sum_of_support_subset _ ((support_finiteProduct_subset a f).trans ha) _ (by simp)]
    simp only [finiteProduct_apply, div_eq_mul_inv]
  have hR (c : ℤ →₀ ℂ) (hc : c.support ⊆ s) : finiteHilbertSquare c n =
      ∑ j ∈ s, c j * (((j : ℂ) - n)⁻¹)^2 := by
    unfold finiteHilbertSquare
    rw [Finsupp.sum_of_support_subset c hc _ (by simp)]
    simp only [div_eq_mul_inv, inv_pow]
  rw [hH, hP, hR _ ((support_finiteProduct_subset a a).trans ha), hR a ha]
  simp only [hH, finiteProduct_apply]
  have he : (∑ j ∈ s, (a j * (∑ k ∈ s, a k * ((k : ℂ) - j)⁻¹)) * ((j : ℂ) - n)⁻¹) =
      ∑ j ∈ s, (a j * ((j : ℂ) - n)⁻¹) * (∑ k ∈ s, a k * ((k : ℂ) - j)⁻¹) := by
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  simpa only [pow_two] using cotlar_sum s a n hn

end NLS.Fourier
