import NLS.Fourier.HilbertNotIsomorphism

/-!
# Failure of the Hilbert isomorphism claim for every finite exponent

For each `1 < p < infinity`, alternating blocks have p-th norm power `N+1`,
while their Hilbert transforms are uniformly bounded. The kernel factorization
cancels all interior terms and leaves two translates of an actual lp sequence.
Consequently the operator is not bounded below, has no continuous linear left
inverse, and is not bijective. The last implication uses the Banach inverse theorem.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier.HilbertLpObstruction
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The decaying factor of the Hilbert kernel, in every lp space above one. -/
def factor (hp1 : 1 < p) : Coeff p := ⟨hilbertKernelFactor, hilbertKernelFactor_memlp hp1⟩

/-- The finite block with coefficient `(-1)^k` for `0 ≤ k ≤ N`. -/
def block (N : ℕ) : Coeff p :=
  ∑ k ∈ Finset.range (N + 1), lp.single p (k : ℤ) ((-1 : ℂ) ^ k)

omit [Fact (1 ≤ p)] in
/-- Its exact p-th norm power grows linearly with the number of coefficients. -/
theorem norm_block_rpow (hp1 : 1 < p) (hp : p ≠ ⊤) (N : ℕ) :
    ‖block (p := p) N‖ ^ p.toReal = (N : ℝ) + 1 := by
  have hd : (Finset.range (N + 1) : Set ℕ).Pairwise (fun i j =>
      Disjoint (Function.support (lp.single p (i : ℤ) ((-1 : ℂ) ^ i)))
        (Function.support (lp.single p (j : ℤ) ((-1 : ℂ) ^ j)))) := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro n hni hnj
    have hi : n = (i : ℤ) := by
      by_contra h
      exact hni (by simp [lp.single_apply, h])
    have hj : n = (j : ℤ) := by
      by_contra h
      exact hnj (by simp [lp.single_apply, h])
    exact hij (by exact_mod_cast hi.symm.trans hj)
  have h := Coeff.norm_sum_rpow_of_disjoint
    (ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp)
    (Finset.range (N + 1)) (fun k => lp.single p (k : ℤ) ((-1 : ℂ) ^ k)) hd
  simpa [block, lp.norm_single (zero_lt_one.trans hp1), norm_pow] using h

section FiniteFormula
variable (hp1 : 1 < p) (H : Coeff p →L[ℂ] Coeff p)
variable (hH : ∀ (a : ℤ →₀ ℂ) (n : ℤ), H (Coeff.ofFinsupp a) n = finiteHilbert a n)
include hp1 hH

/-- The image of one mode is the sum of two translated kernel factors. -/
private theorem transform_single (k : ℤ) (z : ℂ) :
    H (lp.single p k z) = z • (Coeff.shift k (factor hp1) +
      Coeff.shift (k + 1) (factor hp1)) := by
  have hs : lp.single p k z = Coeff.ofFinsupp (Finsupp.single k z) := by
    ext n
    simp [lp.single_apply, Coeff.ofFinsupp_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]
  rw [hs]
  ext n
  rw [hH]
  simp only [finiteHilbert, Finsupp.sum_single_index, zero_div,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_add, Pi.add_apply,
    Coeff.shift_apply, factor]
  rw [show n - (k + 1) = (n - k) - 1 by ring, ← hilbertKernel_factorization, hilbertKernel_sub]
  ring

/-- Interior terms cancel; only two translates of the decaying factor remain. -/
theorem transform_block (N : ℕ) :
    H (block N) = (factor hp1) +
      ((-1 : ℂ) ^ N) • Coeff.shift (N + 1) (factor hp1) := by
  induction N with
  | zero =>
    simp only [block, Nat.zero_add, Finset.sum_range_one, Nat.cast_zero,
      pow_zero, transform_single hp1 H hH, one_smul]
    congr 1
    ext n
    simp
  | succ N ih =>
    have hb : block (N + 1) = block N +
        lp.single p ((N + 1 : ℕ) : ℤ) ((-1 : ℂ) ^ (N + 1)) := by
      unfold block
      rw [Finset.sum_range_succ]
    rw [hb, map_add, ih, transform_single hp1 H hH]
    push_cast
    rw [pow_succ]
    module

/-- A bound independent of the block length. -/
theorem norm_transform_block_le (N : ℕ) :
    ‖H (block N)‖ ≤ 2 * ‖(factor hp1)‖ := by
  rw [transform_block hp1 H hH]
  calc
    _ ≤ ‖(factor hp1)‖ + ‖((-1 : ℂ) ^ N) • Coeff.shift (N + 1) (factor hp1)‖ :=
      norm_add_le _ _
    _ = _ := by simp [norm_smul, norm_pow]; ring


/-- Every finite-exponent realization of the source kernel fails a lower norm bound. -/
theorem not_bounded_below (hp : p ≠ ⊤) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ‖a‖ ≤ C * ‖H a‖ := by
  rintro ⟨C, hC, h⟩
  obtain ⟨N, hN⟩ := exists_nat_gt ((C * (2 * ‖factor hp1‖)) ^ p.toReal)
  have hb := (h (block N)).trans
    (mul_le_mul_of_nonneg_left (norm_transform_block_le hp1 H hH N) hC)
  have hpow := Real.rpow_le_rpow (norm_nonneg _) hb (show 0 ≤ p.toReal from ENNReal.toReal_nonneg)
  rw [norm_block_rpow hp1 hp] at hpow
  linarith

/-- The alternating blocks exclude any continuous linear left inverse. -/
theorem no_left_inverse (hp : p ≠ ⊤) (L : Coeff p →L[ℂ] Coeff p) :
    ¬ Function.LeftInverse L H := by
  intro hL
  apply not_bounded_below hp1 H hH hp
  refine ⟨‖L‖, norm_nonneg _, fun a => ?_⟩
  calc
    ‖a‖ = ‖L (H a)‖ := congrArg norm (hL a).symm
    _ ≤ ‖L‖ * ‖H a‖ := L.le_opNorm _

end FiniteFormula

/-- The source operator is not bijective anywhere in its printed exponent range. -/
theorem transform_not_bijective (hp1 : 1 < p) (hp : p ≠ ⊤) :
    ¬ Function.Bijective (hilbertTransform hp1 hp) := by
  intro h
  let H := hilbertTransform hp1 hp
  let e := ContinuousLinearEquiv.ofBijective H
    (LinearMap.ker_eq_bot.mpr h.1) (LinearMap.range_eq_top.mpr h.2)
  apply no_left_inverse hp1 H (hilbertTransform_finite hp1 hp) hp e.symm.toContinuousLinearMap
  exact e.symm_apply_apply

end NLS.Fourier.HilbertLpObstruction
