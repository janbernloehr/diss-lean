import NLS.MKdV.HierarchyRestriction
import NLS.ZakharovShabat.ClassicalNLSEnergyVariation

/-! # Physical variation and Gardner field of the mKdV energy

The gradient of K₂ is certified by differentiation of its actual integral.
This module treats smooth complex periodic fields, including the real and
purely imaginary reductions, without making a Sobolev extension claim.
-/
noncomputable section
open Complex MeasureTheory NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.MKdV

/-- The physical variational gradient of the independently defined K₂. -/
def classicalMKdVEnergyGradient (u : ℝ → ℂ) : ℝ → ℂ :=
  fun x => -deriv (deriv u) x+2*(u x)^3

/-- An exact complex polynomial expansion of the physical K₂ integral. -/
theorem classicalMKdVEnergy_variation (u h : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hh : ContDiff ℝ ∞ h)
    (hpu : Function.Periodic u 1) (hph : Function.Periodic h 1) (z : ℂ) :
    classicalMKdVEnergy (fun x => u x+z*h x) = classicalMKdVEnergy u +
      z*(∫ x in (0 : ℝ)..1, h x*classicalMKdVEnergyGradient u x) +
      z^2*((1/2 : ℂ)*(∫ x in (0 : ℝ)..1, (deriv h x)^2+6*(u x)^2*(h x)^2)) +
      z^3*(2*(∫ x in (0 : ℝ)..1, u x*(h x)^3)) +
      z^4*((1/2 : ℂ)*(∫ x in (0 : ℝ)..1, (h x)^4)) := by
  have hdu := (contDiff_infty_iff_deriv.mp hu).2
  have hddu := (contDiff_infty_iff_deriv.mp hdu).2
  have hdh := (contDiff_infty_iff_deriv.mp hh).2
  let A := fun x => (deriv u x)^2+(u x)^4
  let B := fun x => 2*deriv u x*deriv h x+4*(u x)^3*h x
  let C := fun x => (deriv h x)^2+6*(u x)^2*(h x)^2
  let D := fun x => 4*u x*(h x)^3
  let E := fun x => (h x)^4
  have hiA : IntervalIntegrable A volume 0 1 :=
    ((hdu.continuous.pow 2).add (hu.continuous.pow 4)).intervalIntegrable 0 1
  have hiB : IntervalIntegrable B volume 0 1 :=
    (((continuous_const.mul hdu.continuous).mul hdh.continuous).add
      ((continuous_const.mul (hu.continuous.pow 3)).mul hh.continuous)).intervalIntegrable 0 1
  have hiC : IntervalIntegrable C volume 0 1 :=
    ((hdh.continuous.pow 2).add
      ((continuous_const.mul (hu.continuous.pow 2)).mul (hh.continuous.pow 2))).intervalIntegrable 0 1
  have hiD : IntervalIntegrable D volume 0 1 :=
    ((continuous_const.mul hu.continuous).mul (hh.continuous.pow 3)).intervalIntegrable 0 1
  have hiE : IntervalIntegrable E volume 0 1 :=
    (hh.continuous.pow 4).intervalIntegrable 0 1
  have hd (x : ℝ) : deriv (fun x => u x+z*h x) x = deriv u x+z*deriv h x :=
    (((contDiff_infty_iff_deriv.mp hu).1 x).hasDerivAt.add
      (((contDiff_infty_iff_deriv.mp hh).1 x).hasDerivAt.const_mul z)).deriv
  have he : (fun x => (deriv (fun y => u y+z*h y) x)^2+(u x+z*h x)^4) =
      fun x => A x+z*B x+z^2*C x+z^3*D x+z^4*E x := by
    funext x; rw [hd]; dsimp [A, B, C, D, E]; ring
  have hiK : IntervalIntegrable (fun x => deriv u x*deriv h x) volume 0 1 :=
    (hdu.continuous.mul hdh.continuous).intervalIntegrable 0 1
  have hiQ : IntervalIntegrable (fun x => (u x)^3*h x) volume 0 1 :=
    ((hu.continuous.pow 3).mul hh.continuous).intervalIntegrable 0 1
  have hiL : IntervalIntegrable (fun x => deriv (deriv u) x*h x) volume 0 1 :=
    (hddu.continuous.mul hh.continuous).intervalIntegrable 0 1
  have hparts := integral_deriv_mul_periodic (deriv u) h hdu hh
    (periodic_deriv_of_periodic u 1 hpu) hph
  have hB : (1/2 : ℂ)*(∫ x in (0 : ℝ)..1, B x) =
      ∫ x in (0 : ℝ)..1, h x*classicalMKdVEnergyGradient u x := by
    have hB' : B = fun x => 2*(deriv u x*deriv h x)+4*((u x)^3*h x) := by
      funext x; dsimp [B]; ring
    have hG : (fun x => h x*classicalMKdVEnergyGradient u x) =
        fun x => -(deriv (deriv u) x*h x)+2*((u x)^3*h x) := by
      funext x; dsimp [classicalMKdVEnergyGradient]; ring
    have hiNegL : IntervalIntegrable (fun x => -(deriv (deriv u) x*h x)) volume 0 1 := by
      simpa only [Pi.neg_apply] using! hiL.neg
    rw [hB', hG, intervalIntegral.integral_add (hiK.const_mul 2) (hiQ.const_mul 4),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hiNegL (hiQ.const_mul 2),
      intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
    linear_combination hparts
  change (1/2 : ℂ)*(∫ x in (0 : ℝ)..1,
    (deriv (fun y => u y+z*h y) x)^2+(u x+z*h x)^4) = _
  rw [he,
    intervalIntegral.integral_add (((hiA.add (hiB.const_mul z)).add (hiC.const_mul (z^2))).add
      (hiD.const_mul (z^3))) (hiE.const_mul (z^4)),
    intervalIntegral.integral_add ((hiA.add (hiB.const_mul z)).add (hiC.const_mul (z^2)))
      (hiD.const_mul (z^3)),
    intervalIntegral.integral_add (hiA.add (hiB.const_mul z)) (hiC.const_mul (z^2)),
    intervalIntegral.integral_add hiA (hiB.const_mul z)]
  simp only [intervalIntegral.integral_const_mul]
  have hD : (∫ x in (0 : ℝ)..1, D x) =
      4*(∫ x in (0 : ℝ)..1, u x*(h x)^3) := by
    have hD' : D = fun x => 4*(u x*(h x)^3) := by funext x; dsimp [D]; ring
    rw [hD', intervalIntegral.integral_const_mul]
  rw [hD, ← hB]
  change (1/2 : ℂ)*((∫ x in (0 : ℝ)..1, A x)+z*(∫ x in (0 : ℝ)..1, B x)+
    z^2*(∫ x in (0 : ℝ)..1, C x)+z^3*(4*(∫ x in (0 : ℝ)..1, u x*(h x)^3))+
    z^4*(∫ x in (0 : ℝ)..1, E x)) =
    (1/2 : ℂ)*(∫ x in (0 : ℝ)..1, A x)+z*((1/2 : ℂ)*(∫ x in (0 : ℝ)..1, B x))+
    z^2*((1/2 : ℂ)*(∫ x in (0 : ℝ)..1, C x))+
    z^3*(2*(∫ x in (0 : ℝ)..1, u x*(h x)^3))+
    z^4*((1/2 : ℂ)*(∫ x in (0 : ℝ)..1, E x))
  ring

/-- The independently defined mKdV energy has this physical first variation. -/
theorem hasDerivAt_classicalMKdVEnergy (u h : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hh : ContDiff ℝ ∞ h)
    (hpu : Function.Periodic u 1) (hph : Function.Periodic h 1) :
    HasDerivAt (fun z : ℂ => classicalMKdVEnergy (fun x => u x+z*h x))
      (∫ x in (0 : ℝ)..1, h x*classicalMKdVEnergyGradient u x) 0 := by
  simp_rw [classicalMKdVEnergy_variation u h hu hh hpu hph]
  simpa using! ((((hasDerivAt_const (0 : ℂ) (classicalMKdVEnergy u)).add
    ((hasDerivAt_id (0 : ℂ)).mul_const
      (∫ x in (0 : ℝ)..1, h x*classicalMKdVEnergyGradient u x))).add
    (((hasDerivAt_id (0 : ℂ)).pow 2).mul_const
      ((1/2 : ℂ)*(∫ x in (0 : ℝ)..1, (deriv h x)^2+6*(u x)^2*(h x)^2)))).add
    (((hasDerivAt_id (0 : ℂ)).pow 3).mul_const
      (2*(∫ x in (0 : ℝ)..1, u x*(h x)^3)))).add
    (((hasDerivAt_id (0 : ℂ)).pow 4).mul_const
      ((1/2 : ℂ)*(∫ x in (0 : ℝ)..1, (h x)^4)))

/-- Gardner's spatial derivative gives the physical complex mKdV expression. -/
theorem deriv_classicalMKdVEnergyGradient (u : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (x : ℝ) :
    deriv (classicalMKdVEnergyGradient u) x =
      -deriv (deriv (deriv u)) x+6*(u x)^2*deriv u x := by
  have hdu := (contDiff_infty_iff_deriv.mp hu).2
  have hddu := (contDiff_infty_iff_deriv.mp hdu).2
  have hd := (((contDiff_infty_iff_deriv.mp hddu).1 x).hasDerivAt.neg).add
    ((((contDiff_infty_iff_deriv.mp hu).1 x).hasDerivAt.pow 3).const_mul 2)
  have hd' : HasDerivAt (classicalMKdVEnergyGradient u)
      (-deriv (deriv (deriv u)) x+2*((3 : ℂ)*(u x)^(3-1)*deriv u x)) x := by
    simpa only [classicalMKdVEnergyGradient, Pi.add_apply, Pi.neg_apply, Pi.pow_apply,
      Nat.cast_ofNat] using! hd
  rw [hd'.deriv]
  norm_num
  ring

end NLS.MKdV
