import NLS.ZakharovShabat.NLSRiccatiResolventGradient

/-! # The all-order physical Lenard recurrence with its exact boundary term

The scalar coupling is independently constructed from the canonical formal
Riccati resolvent. Both spatial rows and its derivative fix the nonlocal
sign and vector factor before imposing any reflection condition.
-/
noncomputable section
open Complex Set MeasureTheory NLS.DifferentialPolynomial MvPolynomial
open scoped ContDiff
namespace NLS.ZakharovShabat

private theorem evaluate_sub' (a b : ℝ → ℂ) (p q : DifferentialPolynomial.Polynomial) :
    evaluate a b (p-q) = evaluate a b p-evaluate a b q := by
  funext x
  simp [evaluate]

private theorem evaluate_two (a b : ℝ → ℂ) :
    evaluate a b (2 : DifferentialPolynomial.Polynomial) = fun _ => 2 := by
  funext x
  simp [evaluate]

def nlsResolventCoefficientCoupling (n : ℕ) : DifferentialPolynomial.Polynomial :=
  PowerSeries.coeff n (riccatiResolventCoupling spatialDerivative (X (false,0)) (X (true,0)))

theorem nlsResolventCoefficientA_succ (n : ℕ) :
    nlsResolventCoefficientA (n+1) = spatialDerivative (nlsResolventCoefficientA n)+
      2*X (true,0)*nlsResolventCoefficientCoupling n :=
  coeff_riccatiResolventA_succ _ _ _ n

theorem nlsResolventCoefficientB_succ (n : ℕ) :
    nlsResolventCoefficientB (n+1) = -spatialDerivative (nlsResolventCoefficientB n)+
      2*X (false,0)*nlsResolventCoefficientCoupling n :=
  coeff_riccatiResolventB_succ _ _ _ n

theorem spatialDerivative_nlsResolventCoefficientCoupling (n : ℕ) :
    spatialDerivative (nlsResolventCoefficientCoupling n) =
      X (true,0)*nlsResolventCoefficientB n-X (false,0)*nlsResolventCoefficientA n :=
  deriv_coeff_riccatiResolventCoupling _ _ _ n

def classicalNLSHierarchyCoupling (a b : ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (-I)^(n+2)*evaluate a b (nlsResolventCoefficientCoupling n) x

def classicalNLSHierarchyRPairing (a b : ℝ → ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  I*a x*(classicalNLSHierarchyGradient a b k x).1+
    (-I*b x)*(classicalNLSHierarchyGradient a b k x).2

theorem deriv_classicalNLSHierarchyGradient_resolvent (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (n : ℕ) (x : ℝ) :
    (deriv (fun y => (classicalNLSHierarchyGradient a b (n+1) y).1) x,
     deriv (fun y => (classicalNLSHierarchyGradient a b (n+1) y).2) x) =
      ((-I)^(n+2)*evaluate a b (spatialDerivative (nlsResolventCoefficientA n)) x,
       (-I)^(n+2)*evaluate a b (spatialDerivative (nlsResolventCoefficientB n)) x) := by
  have h₁ : (fun y => (classicalNLSHierarchyGradient a b (n+1) y).1) =
      fun y => (-I)^(n+2)*evaluate a b (nlsResolventCoefficientA n) y := by
    funext y
    rw [classicalNLSHierarchyGradient_eq_resolvent a b ha hb hpa hpb]
  have h₂ : (fun y => (classicalNLSHierarchyGradient a b (n+1) y).2) =
      fun y => (-I)^(n+2)*evaluate a b (nlsResolventCoefficientB n) y := by
    funext y
    rw [classicalNLSHierarchyGradient_eq_resolvent a b ha hb hpa hpb]
  rw [h₁,h₂]
  exact Prod.ext ((hasDerivAt_evaluate a b ha hb _ x).const_mul _).deriv
    ((hasDerivAt_evaluate a b ha hb _ x).const_mul _).deriv

/-- The all-order actual gradient recurrence, with its constructed coupling. -/
theorem classicalNLSHierarchyGradient_coupled_recurrence (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (n : ℕ) (x : ℝ) :
    (I*(classicalNLSHierarchyGradient a b (n+2) x).1,
     -I*(classicalNLSHierarchyGradient a b (n+2) x).2) =
      (deriv (fun y => (classicalNLSHierarchyGradient a b (n+1) y).1) x+
         2*b x*classicalNLSHierarchyCoupling a b n x,
       deriv (fun y => (classicalNLSHierarchyGradient a b (n+1) y).2) x-
         2*a x*classicalNLSHierarchyCoupling a b n x) := by
  have hd := deriv_classicalNLSHierarchyGradient_resolvent a b ha hb hpa hpb n x
  have hd₁ := congrArg Prod.fst hd
  have hd₂ := congrArg Prod.snd hd
  dsimp only at hd₁ hd₂
  rw [hd₁,hd₂,show n+2=(n+1)+1 by omega,
    classicalNLSHierarchyGradient_eq_resolvent a b ha hb hpa hpb]
  simp only [nlsResolventCoefficientA_succ,nlsResolventCoefficientB_succ,
    evaluate_add,evaluate_neg,evaluate_mul,evaluate_two,evaluate_X,
    Pi.add_apply,Pi.neg_apply,Pi.mul_apply,iteratedDeriv_zero,classicalNLSHierarchyCoupling,
    Bool.false_eq_true,↓reduceIte]
  rw [show n+1+2=(n+2)+1 by omega,pow_succ]
  apply Prod.ext <;> dsimp only <;> ring_nf <;> simp only [I_sq,show I^4=1 by norm_num]
  all_goals ring

theorem hasDerivAt_classicalNLSHierarchyCoupling (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (n : ℕ) (x : ℝ) :
    HasDerivAt (classicalNLSHierarchyCoupling a b n)
      (I*classicalNLSHierarchyRPairing a b (n+1) x) x := by
  have hd := (hasDerivAt_evaluate a b ha hb (nlsResolventCoefficientCoupling n) x).const_mul
    ((-I)^(n+2))
  rw [spatialDerivative_nlsResolventCoefficientCoupling,evaluate_sub',evaluate_mul,evaluate_mul,
    evaluate_X,evaluate_X] at hd
  convert! hd using 1
  rw [classicalNLSHierarchyRPairing,classicalNLSHierarchyGradient_eq_resolvent a b ha hb hpa hpb]
  simp only [Pi.sub_apply,Pi.mul_apply,iteratedDeriv_zero,Bool.false_eq_true,↓reduceIte]
  ring_nf
  simp only [I_sq,show I^4=1 by norm_num]
  ring

theorem classicalNLSHierarchyCoupling_eq_integral (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) (n : ℕ) (x : ℝ) :
    classicalNLSHierarchyCoupling a b n x = classicalNLSHierarchyCoupling a b n 0+
      I*∫ y in (0:ℝ)..x, classicalNLSHierarchyRPairing a b (n+1) y := by
  have hg := (contDiff_classicalNLSHierarchyGradient a b ha hb (n+1)).continuous
  have hc : Continuous (classicalNLSHierarchyRPairing a b (n+1)) := by
    exact (((continuous_const.mul ha.continuous).mul hg.fst).add
      ((continuous_const.mul hb.continuous).mul hg.snd))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hasDerivAt_classicalNLSHierarchyCoupling a b ha hb hpa hpb n y)
    ((continuous_const.mul hc).intervalIntegrable 0 x)
  rw [intervalIntegral.integral_const_mul] at hi
  linear_combination -hi

end NLS.ZakharovShabat
