import NLS.ZakharovShabat.ClassicalNLSFourthHamiltonian
import NLS.ZakharovShabat.NLSHamiltonianReflection
import NLS.ZakharovShabat.NLSRiccatiRescaling

/-! # Physical first variations of the fourth NLS Hamiltonian

The gradients are certified by complex directional derivatives of the actual
Riccati Hamiltonian. They are not assumptions attached to an abstract vector
field. The second variation reuses the physical swap identity.
-/
noncomputable section
open Set Complex MeasureTheory
open scoped ContDiff
namespace NLS.ZakharovShabat

/-- Component variational gradients of the physical fourth Hamiltonian. -/
def classicalNLSFourthGradient (a b : ℝ → ℂ) : (ℝ → ℂ) × (ℝ → ℂ) :=
  (fun x => I * (deriv (deriv (deriv b)) x - 6*a x*b x*deriv b x),
   fun x => -I * (deriv (deriv (deriv a)) x - 6*a x*b x*deriv a x))

/-- The even Hamiltonian is antisymmetric under physical component exchange. -/
theorem classicalNLSHamiltonian_four_swap (a b : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1) :
    classicalNLSHamiltonian b a 4 = -classicalNLSHamiltonian a b 4 := by
  have hn := classicalNLSHamiltonian_field_rescaling b (-a) (-1) 4
  simp only [neg_one_smul, neg_neg] at hn
  have hs := classicalNLSHamiltonian_signedSwap a b ha hb hpa hpb 3
  norm_num at hs
  exact hn.trans hs

/-- Varying the first field gives an exact quadratic complex polynomial. -/
theorem classicalNLSHamiltonian_four_variation_fst (a b h : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hh : ContDiff ℝ ∞ h)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hph : Function.Periodic h 1) (z : ℂ) :
    classicalNLSHamiltonian (fun x => a x+z*h x) b 4 =
      classicalNLSHamiltonian a b 4 +
        z*(∫ x in (0 : ℝ)..1, h x*(classicalNLSFourthGradient a b).1 x) +
        z^2*(-3*I*(∫ x in (0 : ℝ)..1, h x^2*b x*deriv b x)) := by
  have hab : ContDiff ℝ ∞ (fun x => a x+z*h x) := ha.add (contDiff_const.mul hh)
  have hpab : Function.Periodic (fun x => a x+z*h x) 1 := by
    intro x; dsimp only; rw [hpa x, hph x]
  have hdb := (contDiff_infty_iff_deriv.mp hb).2
  have hddb := (contDiff_infty_iff_deriv.mp hdb).2
  have hdddb := (contDiff_infty_iff_deriv.mp hddb).2
  let A := fun x => a x*deriv (deriv (deriv b)) x-3*a x^2*b x*deriv b x
  let B := fun x => h x*(deriv (deriv (deriv b)) x-6*a x*b x*deriv b x)
  let C := fun x => h x^2*b x*deriv b x
  have hiA : IntervalIntegrable A volume 0 1 :=
    ((ha.continuous.mul hdddb.continuous).sub
      ((((continuous_const.mul (ha.continuous.pow 2)).mul hb.continuous).mul
        hdb.continuous))).intervalIntegrable 0 1
  have hiB : IntervalIntegrable B volume 0 1 :=
    (hh.continuous.mul (hdddb.continuous.sub
      ((((continuous_const.mul ha.continuous).mul hb.continuous).mul
        hdb.continuous)))).intervalIntegrable 0 1
  have hiC : IntervalIntegrable C volume 0 1 :=
    (((hh.continuous.pow 2).mul hb.continuous).mul hdb.continuous).intervalIntegrable 0 1
  have hd : (fun x => (a x+z*h x)*deriv (deriv (deriv b)) x -
      3*(a x+z*h x)^2*b x*deriv b x) = fun x => A x+z*B x+(-3*z^2)*C x := by
    funext x; dsimp [A, B, C]; ring
  rw [classicalNLSHamiltonian_four _ b hab hb hpab hpb, hd,
    intervalIntegral.integral_add (hiA.add (hiB.const_mul z)) (hiC.const_mul (-3*z^2)),
    intervalIntegral.integral_add hiA (hiB.const_mul z),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hg : (fun x => h x*(classicalNLSFourthGradient a b).1 x) = fun x => I*B x := by
    funext x; dsimp [classicalNLSFourthGradient, B]; ring
  rw [classicalNLSHamiltonian_four a b ha hb hpa hpb, hg,
    intervalIntegral.integral_const_mul]
  change I*((∫ x in (0 : ℝ)..1, A x)+z*(∫ x in (0 : ℝ)..1, B x)+
    (-3*z^2)*(∫ x in (0 : ℝ)..1, C x)) =
    I*(∫ x in (0 : ℝ)..1, A x)+z*(I*(∫ x in (0 : ℝ)..1, B x))+
      z^2*(-3*I*(∫ x in (0 : ℝ)..1, C x))
  ring

/-- The first gradient is the true component directional derivative of S₄. -/
theorem hasDerivAt_classicalNLSHamiltonian_four_fst (a b h : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hh : ContDiff ℝ ∞ h)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hph : Function.Periodic h 1) :
    HasDerivAt (fun z : ℂ => classicalNLSHamiltonian (fun x => a x+z*h x) b 4)
      (∫ x in (0 : ℝ)..1, h x*(classicalNLSFourthGradient a b).1 x) 0 := by
  simp_rw [classicalNLSHamiltonian_four_variation_fst a b h ha hb hh hpa hpb hph]
  simpa using! ((hasDerivAt_const (0 : ℂ) (classicalNLSHamiltonian a b 4)).add
    ((hasDerivAt_id (0 : ℂ)).mul_const
      (∫ x in (0 : ℝ)..1, h x*(classicalNLSFourthGradient a b).1 x))).add
      (((hasDerivAt_id (0 : ℂ)).pow 2).mul_const
        (-3*I*(∫ x in (0 : ℝ)..1, h x^2*b x*deriv b x)))

/-- The second physical gradient follows from swap antisymmetry. -/
theorem hasDerivAt_classicalNLSHamiltonian_four_snd (a b h : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hh : ContDiff ℝ ∞ h)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hph : Function.Periodic h 1) :
    HasDerivAt (fun z : ℂ => classicalNLSHamiltonian a (fun x => b x+z*h x) 4)
      (∫ x in (0 : ℝ)..1, h x*(classicalNLSFourthGradient a b).2 x) 0 := by
  have he (z : ℂ) : classicalNLSHamiltonian a (fun x => b x+z*h x) 4 =
      -classicalNLSHamiltonian (fun x => b x+z*h x) a 4 :=
    classicalNLSHamiltonian_four_swap _ a (hb.add (contDiff_const.mul hh)) ha
      (by intro x; dsimp only; rw [hpb x, hph x]) hpa
  simp_rw [he]
  have hg : (∫ x in (0 : ℝ)..1, h x*(classicalNLSFourthGradient a b).2 x) =
      -(∫ x in (0 : ℝ)..1, h x*(classicalNLSFourthGradient b a).1 x) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp [classicalNLSFourthGradient]
    ring
  rw [hg]
  exact (hasDerivAt_classicalNLSHamiltonian_four_fst b a h hb ha hh hpb hpa hph).neg

end NLS.ZakharovShabat
