import NLS.MKdV.MiuraCartesianFreeInverse
import NLS.MKdV.CartesianFourierAlgebra

/-! # The actual free Cartesian Jacobian is a Banach isomorphism

Both inverse identities hold on the entire original complex L² space and
the entire native positive-index Cartesian/mean target. No finite-mode
restriction or source reality assumption enters these operator identities.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

private theorem sqrt_two_complex_sq : (Real.sqrt 2 : ℂ)^2 = 2 := by
  exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

theorem miuraCartesianFreeJacobian_signed (n : ℤ) (hn : 0 < n) (h : Coeff 2) :
    miuraPositiveCartesianEval n (miuraCartesianFreeJacobian h) =
      (sourceDiagonalActionRoot (by simp) (by norm_num) n (0 : CoeffPair 2)*(-(h (-n)+h n)/(Real.sqrt 2 : ℂ)),
       -(sourceDiagonalActionRoot (by simp) (by norm_num) n (0 : CoeffPair 2)*((h (-n)-h n)/((Real.sqrt 2 : ℂ)*I)))) := by
  have hi : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn.le
  have hnat : 1 ≤ n.toNat := by omega
  have h := miuraCartesianFreeJacobian_positive n.toNat hnat h
  rw [hi] at h
  simpa only [sourceBirkhoffFourier_fst,sourceBirkhoffFourier_snd,scalarL2Diagonal_fst,scalarL2Diagonal_snd] using! h

/-- Bounded inverse after the actual Jacobian is the identity on all original complex L². -/
theorem miuraCartesianFreeInverse_jacobian (h : Coeff 2) :
    miuraCartesianFreeInverse (miuraCartesianFreeJacobian h) = h := by
  ext n
  by_cases hz : n = 0
  · subst n
    rw [miuraCartesianFreeInverse_mean,miuraCartesianFreeJacobian_mean]
  · by_cases hn : 0 < n
    · rw [miuraCartesianFreeInverse_positive _ n hn]
      have he := miuraCartesianFreeJacobian_signed n hn h
      have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      change (miuraCartesianFreeJacobian h).1.1.val.val n = _ at hx
      change (miuraCartesianFreeJacobian h).1.2.val.val n = _ at hy
      rw [hx,hy]
      exact cartesianFourier_recover_positive _ _ _ _ _ sqrt_two_complex_sq
        (by rw [mul_assoc]; exact miuraFreeInverseSymbol_scaled_mul n hn)
    · have hn' : 0 < -n := by omega
      have he := miuraCartesianFreeJacobian_signed (-n) hn' h
      have hx := congrArg Prod.fst he
      have hy := congrArg Prod.snd he
      change (miuraCartesianFreeJacobian h).1.1.val.val (-n) = _ at hx
      change (miuraCartesianFreeJacobian h).1.2.val.val (-n) = _ at hy
      have hg := miuraCartesianFreeInverse_negative (miuraCartesianFreeJacobian h) (-n) hn'
      rw [neg_neg] at hg
      rw [hg,hx,hy]
      simpa only [neg_neg] using cartesianFourier_recover_negative (Real.sqrt 2 : ℂ)
        (sourceDiagonalActionRoot (by simp) (by norm_num) (-n) (0 : CoeffPair 2))
        (miuraFreeInverseSymbol (-n)*(Weight.sobolev (1/2) (-n) : ℂ)) (h n) (h (-n)) sqrt_two_complex_sq
        (by rw [mul_assoc]; exact miuraFreeInverseSymbol_scaled_mul (-n) hn')

theorem miuraCartesianFreeJacobian_inverse_positive (z : MiuraPositiveCartesianTarget) (n : ℤ) (hn : 0 < n) :
    miuraPositiveCartesianEval n (miuraCartesianFreeJacobian (miuraCartesianFreeInverse z)) =
      (z.1.1.val.val n,z.1.2.val.val n) := by
  rw [miuraCartesianFreeJacobian_signed n hn,miuraCartesianFreeInverse_negative z n hn,
    miuraCartesianFreeInverse_positive z n hn]
  have hm : (miuraFreeInverseSymbol n*(Weight.sobolev (1/2) n : ℂ))*
      sourceDiagonalActionRoot (by simp) (by norm_num) n (0 : CoeffPair 2) = 1 := by
    rw [mul_assoc]
    exact miuraFreeInverseSymbol_scaled_mul n hn
  exact Prod.ext (cartesianFourier_recover_first _ _ _ _ _ sqrt_two_complex_sq hm)
    (cartesianFourier_recover_second _ _ _ _ _ sqrt_two_complex_sq hm)

/-- The actual Jacobian after the bounded inverse is the identity on the
complete natural positive-index weighted Hilbert pair and complex mean. -/
theorem miuraCartesianFreeJacobian_inverse (z : MiuraPositiveCartesianTarget) :
    miuraCartesianFreeJacobian (miuraCartesianFreeInverse z) = z := by
  apply Prod.ext
  · apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      funext n
      by_cases hn : 0 < n
      · exact congrArg Prod.fst (miuraCartesianFreeJacobian_inverse_positive z n hn)
      · exact ((miuraCartesianFreeJacobian (miuraCartesianFreeInverse z)).1.1.property n (by omega)).trans
          (z.1.1.property n (by omega)).symm
    · apply Subtype.ext
      apply Subtype.ext
      funext n
      by_cases hn : 0 < n
      · exact congrArg Prod.snd (miuraCartesianFreeJacobian_inverse_positive z n hn)
      · exact ((miuraCartesianFreeJacobian (miuraCartesianFreeInverse z)).1.2.property n (by omega)).trans
          (z.1.2.property n (by omega)).symm
  · rw [miuraCartesianFreeJacobian_mean,miuraCartesianFreeInverse_mean]

/-- A genuine bounded complex linear equivalence, equal to the actual derivative. -/
def miuraCartesianFreeEquiv : Coeff 2 ≃L[ℂ] MiuraPositiveCartesianTarget where
  toLinearEquiv :=
    { toLinearMap := miuraCartesianFreeJacobian.toLinearMap
      invFun := miuraCartesianFreeInverse
      left_inv := miuraCartesianFreeInverse_jacobian
      right_inv := miuraCartesianFreeJacobian_inverse }
  continuous_toFun := miuraCartesianFreeJacobian.continuous
  continuous_invFun := miuraCartesianFreeInverse.continuous

/-- The original Cartesian sequence vanishes at the free source. -/
theorem miuraL2CartesianSequence_zero : miuraL2CartesianSequence 0 = 0 := by
  have hzero : ∀ j : ℤ, (0 : Coeff 2) j = conj ((0 : Coeff 2) (-j)) := by intro j; simp
  obtain ⟨U,_,h0U,_,hcoord⟩ := exists_local_miuraL2CartesianSequence_analytic 0 hzero
  have he (n : ℤ) : ((miuraL2CartesianSequence 0).1.val n,(miuraL2CartesianSequence 0).2.val n) = 0 := by
    rw [hcoord 0 h0U n]
    simp only [miuraL2CartesianCoefficient,miuraL2CartesianCoordinates_zero,ite_self]
  apply Prod.ext <;> apply Subtype.ext <;> funext n
  · exact congrArg Prod.fst (he n)
  · exact congrArg Prod.snd (he n)

theorem miuraPositiveCartesianMap_zero : miuraPositiveCartesianMap 0 = 0 := by
  change miuraPositiveCartesianProjection (miuraL2CartesianSequence 0,(0 : Coeff 2) 0) = 0
  rw [miuraL2CartesianSequence_zero]
  exact miuraPositiveCartesianProjection.map_zero

end NLS.MKdV
