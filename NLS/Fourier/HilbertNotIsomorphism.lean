import NLS.Fourier.HilbertKernelFactorization
import NLS.Fourier.HilbertBoundedness
import NLS.SequenceSpaces.DisjointCoefficientSums

/-! # The ordinary discrete Hilbert transform has no bounded inverse

Alternating finite blocks have squared norm `N+1`, while their transforms are
uniformly bounded. This refutes the isomorphism assertion of Appendix C.1
already at exponent two, without affecting its valid boundedness assertion.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Fourier

/-- The square-summable factor of the ordinary Hilbert kernel. -/
def hilbertFactorCoeffs : Coeff 2 :=
  ⟨hilbertKernelFactor, hilbertKernelFactor_memlp (by norm_num)⟩

/-- A block of `N+1` alternating unit coefficients. -/
def alternatingHilbertBlock (N : ℕ) : Coeff 2 :=
  ∑ k ∈ Finset.range (N+1), lp.single 2 (k:ℤ) ((-1:ℂ)^k)

/-- The input blocks have unbounded norms. -/
theorem norm_alternatingHilbertBlock_sq (N : ℕ) :
    ‖alternatingHilbertBlock N‖^2 = (N:ℝ)+1 := by
  have hd : (Finset.range (N+1) : Set ℕ).Pairwise (fun i j =>
      Disjoint (Function.support (lp.single 2 (i:ℤ) ((-1:ℂ)^i)))
        (Function.support (lp.single 2 (j:ℤ) ((-1:ℂ)^j)))) := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro n hni hnj
    have hi : n = (i:ℤ) := by
      by_contra h
      exact hni (by simp [lp.single_apply, h])
    have hj : n = (j:ℤ) := by
      by_contra h
      exact hnj (by simp [lp.single_apply, h])
    exact hij (by exact_mod_cast hi.symm.trans hj)
  have h := Coeff.norm_sum_rpow_of_disjoint (by norm_num : 0 < (2:ℝ≥0∞).toReal)
    (Finset.range (N+1)) (fun k => lp.single 2 (k:ℤ) ((-1:ℂ)^k)) hd
  simpa [alternatingHilbertBlock, lp.norm_single, norm_pow] using h

section FiniteFormula
variable (H : Coeff 2 →L[ℂ] Coeff 2)
variable (hH : ∀ (a : ℤ →₀ ℂ) (n : ℤ), H (Coeff.ofFinsupp a) n = finiteHilbert a n)
include hH

private theorem transform_single (k : ℤ) (z : ℂ) :
    H (lp.single 2 k z) = z • (Coeff.shift k hilbertFactorCoeffs +
      Coeff.shift (k+1) hilbertFactorCoeffs) := by
  have hs : lp.single 2 k z = Coeff.ofFinsupp (Finsupp.single k z) := by
    ext n
    simp [lp.single_apply, Coeff.ofFinsupp_apply, Pi.single_apply, Finsupp.single_apply, eq_comm]
  rw [hs]
  ext n
  rw [hH]
  simp only [finiteHilbert, Finsupp.sum_single_index, zero_div,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_add, Pi.add_apply,
    Coeff.shift_apply, hilbertFactorCoeffs]
  rw [show n-(k+1) = (n-k)-1 by ring, ← hilbertKernel_factorization, hilbertKernel_sub]
  ring

/-- Interior terms cancel; only two translates of the decaying factor remain. -/
theorem transform_alternatingHilbertBlock (N : ℕ) :
    H (alternatingHilbertBlock N) = hilbertFactorCoeffs +
      ((-1:ℂ)^N) • Coeff.shift (N+1) hilbertFactorCoeffs := by
  induction N with
  | zero =>
    simp only [alternatingHilbertBlock, Nat.zero_add, Finset.sum_range_one, Nat.cast_zero,
      pow_zero, transform_single H hH, one_smul]
    congr 1
    ext n
    simp
  | succ N ih =>
    have hb : alternatingHilbertBlock (N+1) = alternatingHilbertBlock N +
        lp.single 2 ((N+1:ℕ):ℤ) ((-1:ℂ)^(N+1)) := by
      unfold alternatingHilbertBlock
      rw [Finset.sum_range_succ]
    rw [hb, map_add, ih, transform_single H hH]
    push_cast
    rw [pow_succ]
    module

/-- A bound independent of the block length. -/
theorem norm_transform_alternatingHilbertBlock_le (N : ℕ) :
    ‖H (alternatingHilbertBlock N)‖ ≤ 2*‖hilbertFactorCoeffs‖ := by
  rw [transform_alternatingHilbertBlock H hH]
  calc
    _ ≤ ‖hilbertFactorCoeffs‖ + ‖((-1:ℂ)^N) • Coeff.shift (N+1) hilbertFactorCoeffs‖ :=
      norm_add_le _ _
    _ = _ := by simp [norm_smul, norm_pow]; ring

/-- No uniform lower norm estimate can hold for the ordinary transform. -/
theorem not_bounded_below_of_hilbert_finite_formula :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ‖a‖ ≤ C*‖H a‖ := by
  rintro ⟨C,hC,h⟩
  obtain ⟨N,hN⟩ := exists_nat_gt ((2*C*‖hilbertFactorCoeffs‖)^2)
  have hb := (h (alternatingHilbertBlock N)).trans
    (mul_le_mul_of_nonneg_left (norm_transform_alternatingHilbertBlock_le H hH N) hC)
  have hs := norm_alternatingHilbertBlock_sq N
  have hp : 0 ≤ ‖alternatingHilbertBlock N‖ := norm_nonneg _
  nlinarith [sq_nonneg (C*(2*‖hilbertFactorCoeffs‖)-‖alternatingHilbertBlock N‖)]

/-- In particular, no bounded linear left inverse exists. -/
theorem no_left_inverse_of_hilbert_finite_formula (L : Coeff 2 →L[ℂ] Coeff 2) :
    ¬ Function.LeftInverse L H := by
  intro hL
  apply not_bounded_below_of_hilbert_finite_formula H hH
  refine ⟨‖L‖,norm_nonneg _,fun a => ?_⟩
  calc
    ‖a‖ = ‖L (H a)‖ := congrArg norm (hL a).symm
    _ ≤ ‖L‖*‖H a‖ := L.le_opNorm _

end FiniteFormula

/-- Appendix C.1's Hilbert-space operator is not bounded below. -/
theorem discreteHilbert_not_bounded_below :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ a, ‖a‖ ≤ C*‖discreteHilbert a‖ :=
  not_bounded_below_of_hilbert_finite_formula discreteHilbert discreteHilbert_finite

/-- The completed full-range transform also has no bounded inverse at p=2. -/
theorem hilbertTransform_two_no_left_inverse (L : Coeff 2 →L[ℂ] Coeff 2) :
    ¬ Function.LeftInverse L (hilbertTransform (p := 2) (by norm_num) (by norm_num)) :=
  no_left_inverse_of_hilbert_finite_formula _ (hilbertTransform_finite _ _) L

/-- No continuous linear equivalence can realize the source's transform at p=2. -/
theorem hilbertTransform_two_ne_equiv (e : Coeff 2 ≃L[ℂ] Coeff 2) :
    hilbertTransform (p := 2) (by norm_num) (by norm_num) ≠ e.toContinuousLinearMap := by
  intro h
  apply hilbertTransform_two_no_left_inverse e.symm.toContinuousLinearMap
  intro a
  rw [h]
  exact e.symm_apply_apply a

end NLS.Fourier
