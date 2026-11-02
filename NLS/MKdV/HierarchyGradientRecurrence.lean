import NLS.ZakharovShabat.NLSRiccatiResolventGradient

/-! # The all-order physical gradient recurrence on the diagonal -/
noncomputable section
open NLS.DifferentialPolynomial NLS.ZakharovShabat MvPolynomial Complex
open scoped ContDiff
namespace NLS.MKdV

private def diagonalPolynomialMap : DifferentialPolynomial.Polynomial →ₐ[ℂ]
    DifferentialPolynomial.Polynomial := renameFields (fun _ : Bool => false)

private theorem diagonalPolynomialMap_D (p : DifferentialPolynomial.Polynomial) :
    diagonalPolynomialMap (spatialDerivative p) = spatialDerivative (diagonalPolynomialMap p) :=
  renameFields_spatialDerivative (fun _ : Bool => false) p

private theorem diagonalPolynomialMap_X (v : Jet) :
    diagonalPolynomialMap (X v) = X (false,v.2) := by simp [diagonalPolynomialMap, renameFields]

private theorem diagonalPolynomialMap_A (n : ℕ) :
    diagonalPolynomialMap (nlsResolventCoefficientA n) = PowerSeries.coeff n
      (riccatiResolventA spatialDerivative (X (false,0)) (X (false,0))) := by
  have he := congrArg (PowerSeries.coeff n) (map_riccatiResolventA spatialDerivative
    spatialDerivative diagonalPolynomialMap.toRingHom diagonalPolynomialMap_D (X (false,0)) (X (true,0)))
  change diagonalPolynomialMap (nlsResolventCoefficientA n) = PowerSeries.coeff n
    (riccatiResolventA spatialDerivative
      (diagonalPolynomialMap (X (false,0))) (diagonalPolynomialMap (X (true,0)))) at he
  simpa only [diagonalPolynomialMap_X] using he

private theorem diagonalPolynomialMap_B (n : ℕ) :
    diagonalPolynomialMap (nlsResolventCoefficientB n) = PowerSeries.coeff n
      (riccatiResolventB spatialDerivative (X (false,0)) (X (false,0))) := by
  have he := congrArg (PowerSeries.coeff n) (map_riccatiResolventB spatialDerivative
    spatialDerivative diagonalPolynomialMap.toRingHom diagonalPolynomialMap_D (X (false,0)) (X (true,0)))
  change diagonalPolynomialMap (nlsResolventCoefficientB n) = PowerSeries.coeff n
    (riccatiResolventB spatialDerivative
      (diagonalPolynomialMap (X (false,0))) (diagonalPolynomialMap (X (true,0)))) at he
  simpa only [diagonalPolynomialMap_X] using he

private theorem evaluate_diagonalPolynomialMap (u : ℝ → ℂ) (p : DifferentialPolynomial.Polynomial) :
    evaluate u u (diagonalPolynomialMap p) = evaluate u u p := by
  funext x
  change MvPolynomial.eval₂ (RingHom.id ℂ) _ (MvPolynomial.rename _ p) = _
  rw [MvPolynomial.eval₂_rename]
  simp only [evaluate, Function.comp_def, ite_self]
  rfl

theorem evaluate_nlsResolventA_odd_diagonal (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (m : ℕ) :
    evaluate u u (nlsResolventCoefficientA (2*m+1)) =
      deriv (evaluate u u (nlsResolventCoefficientA (2*m))) := by
  have hp : diagonalPolynomialMap (nlsResolventCoefficientA (2*m+1)) =
      spatialDerivative (diagonalPolynomialMap (nlsResolventCoefficientA (2*m))) := by
    rw [diagonalPolynomialMap_A, diagonalPolynomialMap_A]
    exact coeff_riccatiResolventA_odd_diagonal spatialDerivative (X (false,0)) m
  have he := congrArg (evaluate u u) hp
  rw [evaluate_diagonalPolynomialMap, evaluate_spatialDerivative u u hu hu,
    evaluate_diagonalPolynomialMap] at he
  exact he

theorem evaluate_nlsResolventB_odd_diagonal (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (m : ℕ) :
    evaluate u u (nlsResolventCoefficientB (2*m+1)) =
      -deriv (evaluate u u (nlsResolventCoefficientB (2*m))) := by
  have hp : diagonalPolynomialMap (nlsResolventCoefficientB (2*m+1)) =
      -spatialDerivative (diagonalPolynomialMap (nlsResolventCoefficientB (2*m))) := by
    rw [diagonalPolynomialMap_B, diagonalPolynomialMap_B]
    exact coeff_riccatiResolventB_odd_diagonal spatialDerivative (X (false,0)) m
  have he := congrArg (evaluate u u) hp
  rw [evaluate_diagonalPolynomialMap, evaluate_neg, evaluate_spatialDerivative u u hu hu,
    evaluate_diagonalPolynomialMap] at he
  exact he

/-- The corrected R=diag(i,-i) recurrence for the actual physical gradients,
at every order on smooth complex periodic diagonal inputs. -/
theorem classicalHierarchyGradient_diagonal_recurrence (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hpu : Function.Periodic u 1) (m : ℕ) (x : ℝ) :
    (I*(classicalNLSHierarchyGradient u u (2*m+2) x).1,
      -I*(classicalNLSHierarchyGradient u u (2*m+2) x).2) =
      (deriv (fun y => (classicalNLSHierarchyGradient u u (2*m+1) y).1) x,
        deriv (fun y => (classicalNLSHierarchyGradient u u (2*m+1) y).2) x) := by
  have ha : (fun y => (classicalNLSHierarchyGradient u u (2*m+1) y).1) =
      fun y => (-I)^(2*m+2)*evaluate u u (nlsResolventCoefficientA (2*m)) y := by
    funext y
    rw [classicalNLSHierarchyGradient_eq_resolvent u u hu hu hpu hpu]
  have hb : (fun y => (classicalNLSHierarchyGradient u u (2*m+1) y).2) =
      fun y => (-I)^(2*m+2)*evaluate u u (nlsResolventCoefficientB (2*m)) y := by
    funext y
    rw [classicalNLSHierarchyGradient_eq_resolvent u u hu hu hpu hpu]
  rw [show 2*m+2 = (2*m+1)+1 by omega,
    classicalNLSHierarchyGradient_eq_resolvent u u hu hu hpu hpu, ha, hb,
    deriv_const_mul_field, deriv_const_mul_field]
  simp only [evaluate_nlsResolventA_odd_diagonal u hu,
    evaluate_nlsResolventB_odd_diagonal u hu, Pi.neg_apply]
  rw [show 2*m+1+2 = (2*m+2)+1 by omega, pow_succ]
  apply Prod.ext <;> dsimp only <;> ring_nf <;> simp [I_sq]

end NLS.MKdV
