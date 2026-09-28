import NLS.SequenceSpaces.DeletedOperatorExtension

/-!
# Inverse bounds for nearby deleted-coordinate operators

The proof of Lemma 12.10 compares deleted-index Jacobians after
extending them to a common sequence space. This file records the
quantitative perturbation step: if an invertible extension is close
enough to a fixed invertible operator, its deleted-block inverse has
a bound independent of the deleted index.
-/

noncomputable section
open scoped ENNReal

namespace NLS

/-- An already invertible operator close to a fixed invertible operator
has inverse norm at most twice the norm of the fixed inverse. -/
theorem inverse_norm_le_two_mul_of_near
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T S R R₀ : E →L[ℂ] E)
    (hTR : T.comp R = ContinuousLinearMap.id ℂ E)
    (hR₀S : R₀.comp S = ContinuousLinearMap.id ℂ E)
    (hnear : ‖R₀‖ * ‖S - T‖ ≤ (1 / 2 : ℝ)) :
    ‖R‖ ≤ 2 * ‖R₀‖ := by
  apply ContinuousLinearMap.opNorm_le_bound R (by positivity)
  intro y
  have hTy : T (R y) = y := by
    have h := congrArg (fun A : E →L[ℂ] E => A y) hTR
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using h
  have hR₀S_apply (x : E) : R₀ (S x) = x := by
    have h := congrArg (fun A : E →L[ℂ] E => A x) hR₀S
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using h
  have hidentity : R y = R₀ y + R₀ ((S - T) (R y)) := by
    calc
      R y = R₀ (S (R y)) := (hR₀S_apply _).symm
      _ = R₀ (T (R y) + (S - T) (R y)) := by simp
      _ = R₀ y + R₀ ((S - T) (R y)) := by rw [map_add, hTy]
  have hbound : ‖R y‖ ≤
      ‖R₀‖ * ‖y‖ + (‖R₀‖ * ‖S - T‖) * ‖R y‖ := by
    calc
      ‖R y‖ = ‖R₀ y + R₀ ((S - T) (R y))‖ := congrArg norm hidentity
      ‖R₀ y + R₀ ((S - T) (R y))‖ ≤
          ‖R₀ y‖ + ‖R₀ ((S - T) (R y))‖ := norm_add_le _ _
      _ ≤ ‖R₀‖ * ‖y‖ +
          ‖R₀‖ * (‖S - T‖ * ‖R y‖) := by
            apply add_le_add (R₀.le_opNorm y)
            exact (R₀.le_opNorm _).trans
              (mul_le_mul_of_nonneg_left ((S - T).le_opNorm _) (norm_nonneg _))
      _ = ‖R₀‖ * ‖y‖ +
          (‖R₀‖ * ‖S - T‖) * ‖R y‖ := by ring
  have hsmall : (‖R₀‖ * ‖S - T‖) * ‖R y‖ ≤
      (1 / 2 : ℝ) * ‖R y‖ :=
    mul_le_mul_of_nonneg_right hnear (norm_nonneg _)
  nlinarith

end NLS

namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The explicit inverse of a deleted Jacobian extension is the
extension of the deleted-block inverse with scalar `1/2`. -/
theorem deletedJacobianExtension_inverse_comp (n : ℤ)
    (Q R : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (hQR : Q.comp R = ContinuousLinearMap.id ℂ (DeletedCoeff p n)) :
    (deletedJacobianExtension n Q).comp
        (deletedOperatorExtension n (1 / 2 : ℂ) R) =
      ContinuousLinearMap.id ℂ (Coeff p) := by
  change (deletedOperatorExtension n 2 Q).comp
    (deletedOperatorExtension n (1 / 2 : ℂ) R) = _
  rw [deletedOperatorExtension_comp, hQR]
  norm_num

/-- A deleted-block inverse is controlled by the inverse of a fixed
full-space operator when its extension is sufficiently close to that
operator. The bound has no dependence on the deleted index. -/
theorem norm_deleted_inverse_le_two_mul_of_extension_near
    (n : ℤ) (Q R : DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (S R₀ : Coeff p →L[ℂ] Coeff p)
    (hQR : Q.comp R = ContinuousLinearMap.id ℂ (DeletedCoeff p n))
    (hR₀S : R₀.comp S = ContinuousLinearMap.id ℂ (Coeff p))
    (hnear : ‖R₀‖ * ‖S - deletedJacobianExtension n Q‖ ≤
      (1 / 2 : ℝ)) :
    ‖R‖ ≤ 2 * ‖R₀‖ := by
  have hblock := norm_deletedOperator_le_norm_extension n (1 / 2 : ℂ) R
  have hfull := NLS.inverse_norm_le_two_mul_of_near
    (deletedJacobianExtension n Q) S
    (deletedOperatorExtension n (1 / 2 : ℂ) R) R₀
    (deletedJacobianExtension_inverse_comp n Q R hQR) hR₀S hnear
  exact hblock.trans hfull

/-- Convergence of the block extensions to one invertible operator
gives a common inverse bound outside a finite set of deleted indices.
The finitely many remaining inverses can later be bounded separately. -/
theorem eventually_norm_deleted_inverse_le_two_mul_of_extension_converges
    (Q R : (n : ℤ) → DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (S R₀ : Coeff p →L[ℂ] Coeff p)
    (hQR : ∀ n, (Q n).comp (R n) =
      ContinuousLinearMap.id ℂ (DeletedCoeff p n))
    (hR₀S : R₀.comp S = ContinuousLinearMap.id ℂ (Coeff p))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ n : ℤ,
      K ≤ n.natAbs → ‖S - deletedJacobianExtension n (Q n)‖ < ε) :
    ∃ K : ℕ, ∀ n : ℤ, K ≤ n.natAbs → ‖R n‖ ≤ 2 * ‖R₀‖ := by
  have hε : 0 < (1 / (2 * (‖R₀‖ + 1)) : ℝ) := by positivity
  obtain ⟨K,hK⟩ := hconv _ hε
  refine ⟨K, ?_⟩
  intro n hn
  have hnorm : ‖S - deletedJacobianExtension n (Q n)‖ ≤
      (1 / (2 * (‖R₀‖ + 1)) : ℝ) := le_of_lt (hK n hn)
  have hnear : ‖R₀‖ * ‖S - deletedJacobianExtension n (Q n)‖ ≤
      (1 / 2 : ℝ) := by
    calc
      ‖R₀‖ * ‖S - deletedJacobianExtension n (Q n)‖ ≤
          ‖R₀‖ * (1 / (2 * (‖R₀‖ + 1)) : ℝ) :=
        mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ ≤ (‖R₀‖ + 1) * (1 / (2 * (‖R₀‖ + 1)) : ℝ) := by
        gcongr
        linarith [norm_nonneg R₀]
      _ = 1 / 2 := by
        have hpos : ‖R₀‖ + 1 ≠ (0 : ℝ) := by positivity
        field_simp
  exact norm_deleted_inverse_le_two_mul_of_extension_near
    n (Q n) (R n) S R₀ (hQR n) hR₀S hnear

/-- The inverse norms are bounded at *every* deleted index: the
convergence estimate handles the tail and finite boundedness handles
the remaining indices. -/
theorem exists_uniform_norm_deleted_inverse_of_extension_converges
    (Q R : (n : ℤ) → DeletedCoeff p n →L[ℂ] DeletedCoeff p n)
    (S R₀ : Coeff p →L[ℂ] Coeff p)
    (hQR : ∀ n, (Q n).comp (R n) =
      ContinuousLinearMap.id ℂ (DeletedCoeff p n))
    (hR₀S : R₀.comp S = ContinuousLinearMap.id ℂ (Coeff p))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ n : ℤ,
      K ≤ n.natAbs → ‖S - deletedJacobianExtension n (Q n)‖ < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℤ, ‖R n‖ ≤ M := by
  obtain ⟨K,hK⟩ :=
    eventually_norm_deleted_inverse_le_two_mul_of_extension_converges
      Q R S R₀ hQR hR₀S hconv
  let head : Set ℤ := {n | n.natAbs < K}
  have hhead : head.Finite := by
    apply (Set.finite_Icc (-(K : ℤ)) (K : ℤ)).subset
    intro n hn
    have hnat : (n.natAbs : ℤ) ≤ K := by
      exact_mod_cast (Nat.le_of_lt hn)
    have habs : |n| ≤ (K : ℤ) := by
      simpa only [Int.natCast_natAbs] using hnat
    exact abs_le.mp habs
  obtain ⟨B,hB⟩ : BddAbove ((fun n : ℤ => ‖R n‖) '' head) :=
    (hhead.image (fun n => ‖R n‖)).bddAbove
  refine ⟨max B (2 * ‖R₀‖), le_max_of_le_right (by positivity), ?_⟩
  intro n
  by_cases hn : K ≤ n.natAbs
  · exact (hK n hn).trans (le_max_right _ _)
  · have hnhead : n ∈ head := Nat.lt_of_not_ge hn
    exact (hB ⟨n,hnhead,rfl⟩).trans (le_max_left _ _)

end NLS.Coeff
