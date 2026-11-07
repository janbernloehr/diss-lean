import NLS.ZakharovShabat.NLSHierarchyNonlocalRecurrence
import NLS.DifferentialPolynomial.RiccatiResolventReflection
import NLS.DifferentialPolynomial.SignedSpatialJetReflection

/-! # The exact vanishing boundary coupling for both spatial reflection signs -/
noncomputable section
open Complex MvPolynomial NLS.DifferentialPolynomial
open scoped ContDiff
namespace NLS.ZakharovShabat

theorem signedSpatialJetReflection_evenCoupling (ε : ℂ) (hε : ε=1 ∨ ε = -1) (m : ℕ) :
    signedSpatialJetReflection ε (nlsResolventCoefficientCoupling (2*m)) =
      -nlsResolventCoefficientCoupling (2*m) := by
  have he := congrArg (PowerSeries.coeff (2*m))
    (map_riccatiResolventCoupling spatialDerivative (-spatialDerivative)
      (signedSpatialJetReflection ε).toRingHom (signedSpatialJetReflection_spatialDerivative ε)
      (X (false,0)) (X (true,0)))
  change signedSpatialJetReflection ε (nlsResolventCoefficientCoupling (2*m)) =
    PowerSeries.coeff (2*m) (riccatiResolventCoupling (-spatialDerivative)
      (signedSpatialJetReflection ε (X (false,0)))
      (signedSpatialJetReflection ε (X (true,0)))) at he
  simp only [signedSpatialJetReflection_X,pow_zero,mul_one] at he
  rcases hε with rfl | rfl
  · simpa only [map_one,one_mul,coeff_riccatiResolventCoupling_even_neg_derivation,
      nlsResolventCoefficientCoupling] using he
  · simpa only [map_neg,map_one,neg_one_mul,riccatiResolventCoupling_neg_fields,
      coeff_riccatiResolventCoupling_even_neg_derivation,nlsResolventCoefficientCoupling] using he

theorem classicalNLSHierarchyCoupling_midpointReflection (ε : ℂ) (hε : ε=1 ∨ ε = -1)
    (a b : ℝ → ℂ) (m : ℕ) (x : ℝ) :
    classicalNLSHierarchyCoupling (fun y => ε*a (1-y)) (fun y => ε*b (1-y)) (2*m) x =
      -classicalNLSHierarchyCoupling a b (2*m) (1-x) := by
  unfold classicalNLSHierarchyCoupling
  rw [evaluate_signedSpatialJetReflection,signedSpatialJetReflection_evenCoupling ε hε,
    evaluate_neg]
  simp only [Pi.neg_apply,mul_neg]

theorem classicalNLSHierarchyCoupling_zero_of_midpointReflection
    (ε : ℂ) (hε : ε=1 ∨ ε = -1) (a b : ℝ → ℂ)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hTa : ∀ x, ε*a (1-x)=a x) (hTb : ∀ x, ε*b (1-x)=b x) (m : ℕ) :
    classicalNLSHierarchyCoupling a b (2*m) 0 = 0 := by
  have he := classicalNLSHierarchyCoupling_midpointReflection ε hε a b m 0
  rw [funext hTa,funext hTb,sub_zero] at he
  have hp : classicalNLSHierarchyCoupling a b (2*m) 1 =
      classicalNLSHierarchyCoupling a b (2*m) 0 := by
    unfold classicalNLSHierarchyCoupling
    rw [show (1:ℝ)=0+1 by norm_num,periodic_evaluate a b 1 hpa hpb]
  rw [hp] at he
  linear_combination (1/2:ℂ)*he

end NLS.ZakharovShabat
