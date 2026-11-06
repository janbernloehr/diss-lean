import NLS.ZakharovShabat.ClassicalNLSEnergyVariation

/-! # The fourth physical NLS Hamiltonian

The original Riccati definition gives the article's explicit S₄ integral.
All derivatives and integrals below have the original period-one convention.
-/
noncomputable section
open Set Complex MeasureTheory intervalIntegral
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- The fourth Riccati coefficient in the original smooth fields. -/
theorem nlsRiccatiDensity_three (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    nlsRiccatiDensity a b 3 = fun x =>
      -deriv (deriv (deriv b)) x + deriv a x * b x^2 + 4*a x*b x*deriv b x := by
  have hanti : Finset.antidiagonal 1 = {(0,1), (1,0)} := by decide
  rw [nlsRiccatiDensity_succ_succ a b 1, hanti]
  simp only [Finset.sum_insert (show (0,1) ∉ ({(1,0)} : Finset (ℕ × ℕ)) by decide),
    Finset.sum_singleton, Nat.reduceAdd, nlsRiccatiDensity_two,
    nlsRiccatiDensity_zero, nlsRiccatiDensity_one]
  have hdb := (contDiff_infty_iff_deriv.mp hb).2
  have hddb := (contDiff_infty_iff_deriv.mp hdb).2
  ext x
  have hd := (((contDiff_infty_iff_deriv.mp hddb).1 x).hasDerivAt.neg).add
    (((contDiff_infty_iff_deriv.mp ha).1 x).hasDerivAt.mul
      (((contDiff_infty_iff_deriv.mp hb).1 x).hasDerivAt.pow 2))
  change deriv (-deriv (deriv b) + a*b^2) x +
    a x*((-b x)*(-deriv b x)+(-deriv b x)*(-b x)) = _
  rw [hd.deriv]
  norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one, Pi.pow_apply]
  ring

/-- The fourth physical Hamiltonian has the article's exact S₄ sign and factor. -/
theorem classicalNLSHamiltonian_four (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) :
    classicalNLSHamiltonian a b 4 = I * ∫ x in (0 : ℝ)..1,
      a x * deriv (deriv (deriv b)) x - 3*a x^2*b x*deriv b x := by
  have hda := (contDiff_infty_iff_deriv.mp ha).2
  have hdb := (contDiff_infty_iff_deriv.mp hb).2
  have hddb := (contDiff_infty_iff_deriv.mp hdb).2
  have hdddb := (contDiff_infty_iff_deriv.mp hddb).2
  let A := fun x => a x * deriv (deriv (deriv b)) x
  let B := fun x => a x * deriv a x * b x^2
  let C := fun x => a x^2*b x*deriv b x
  have hiA : IntervalIntegrable A volume 0 1 :=
    (ha.continuous.mul hdddb.continuous).intervalIntegrable 0 1
  have hiB : IntervalIntegrable B volume 0 1 :=
    ((ha.continuous.mul hda.continuous).mul (hb.continuous.pow 2)).intervalIntegrable 0 1
  have hiC : IntervalIntegrable C volume 0 1 :=
    (((ha.continuous.pow 2).mul hb.continuous).mul hdb.continuous).intervalIntegrable 0 1
  have hparts := integral_deriv_mul_periodic (a*a) (b*b) (ha.mul ha) (hb.mul hb)
    (hpa.mul hpa) (hpb.mul hpb)
  have hprod (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (x : ℝ) :
      deriv (f*f) x = 2*f x*deriv f x := by
    rw [deriv_mul ((contDiff_infty_iff_deriv.mp hf).1 x)
      ((contDiff_infty_iff_deriv.mp hf).1 x)]
    ring
  have hpB : (fun x => deriv (a*a) x * (b*b) x) = fun x => 2*B x := by
    funext x; rw [hprod a ha]; dsimp [B]; ring
  have hpC : (fun x => (a*a) x * deriv (b*b) x) = fun x => 2*C x := by
    funext x; rw [hprod b hb]; dsimp [C]; ring
  rw [hpB, hpC, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hparts
  have hBC : (∫ x in (0 : ℝ)..1, B x) = -(∫ x in (0 : ℝ)..1, C x) := by
    linear_combination hparts / 2
  have hd : (fun x => a x * nlsRiccatiDensity a b 3 x) =
      fun x => -A x+B x+4*C x := by
    rw [nlsRiccatiDensity_three a b ha hb]
    funext x; dsimp [A, B, C]; ring
  change (-I)^5 * (∫ x in (0 : ℝ)..1, a x*nlsRiccatiDensity a b 3 x) = _
  have hiNegA : IntervalIntegrable (fun x => -A x) volume 0 1 := by
    simpa only [Pi.neg_apply] using! hiA.neg
  rw [hd, intervalIntegral.integral_add (hiNegA.add hiB) (hiC.const_mul 4),
    intervalIntegral.integral_add hiNegA hiB, intervalIntegral.integral_neg, intervalIntegral.integral_const_mul, hBC]
  have hr : (fun x => a x * deriv (deriv (deriv b)) x - 3*a x^2*b x*deriv b x) =
      fun x => A x-3*C x := by funext x; dsimp [A, C]; ring
  rw [hr, intervalIntegral.integral_sub hiA (hiC.const_mul 3), intervalIntegral.integral_const_mul]
  norm_num [pow_succ, I_sq]
  ring

end NLS.ZakharovShabat
