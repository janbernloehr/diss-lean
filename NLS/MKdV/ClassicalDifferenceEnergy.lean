import NLS.ZakharovShabat.ClassicalNLSEnergyVariation
import NLS.ZakharovShabat.SobolevPhysicalJets

/-! # Periodic difference-energy identities for scalar mKdV

The third derivative and constant translation contribute zero bilinear
energy. Periodic integration by parts moves the derivative off the
difference in the cubic term, leaving a bounded coefficient times its square.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory NLS.ZakharovShabat
open scoped ContDiff ComplexConjugate
namespace NLS.MKdV

def scalarClassicalMKdVField (M : ℂ) (u : ℝ → ℂ) (x : ℝ) : ℂ :=
  -deriv (deriv (deriv u)) x+6*((u x)^2-M)*deriv u x

theorem integral_mul_deriv_periodic_zero (w : ℝ → ℂ)
    (hw : ContDiff ℝ ∞ w) (hp : Function.Periodic w 1) :
    (∫ x in (0:ℝ)..1, w x*deriv w x) = 0 := by
  have h := integral_deriv_mul_periodic w w hw hw hp hp
  have he : (fun x => deriv w x*w x) = (fun x => w x*deriv w x) := funext (fun x => mul_comm _ _)
  rw [he] at h
  linear_combination (1/2:ℂ)*h

theorem integral_mul_deriv3_periodic_zero (w : ℝ → ℂ)
    (hw : ContDiff ℝ ∞ w) (hp : Function.Periodic w 1) :
    (∫ x in (0:ℝ)..1, w x*deriv (deriv (deriv w)) x) = 0 := by
  have hw1 := (contDiff_infty_iff_deriv.mp hw).2
  have hw2 := (contDiff_infty_iff_deriv.mp hw1).2
  have hp1 := periodic_deriv_of_periodic w 1 hp
  have hp2 := periodic_deriv_of_periodic (deriv w) 1 hp1
  have hz := integral_mul_deriv_periodic_zero (deriv w) hw1 hp1
  have h := integral_deriv_mul_periodic w (deriv (deriv w)) hw hw2 hp hp2
  rw [hz] at h
  linear_combination h

theorem integral_weighted_mul_deriv_periodic (a w : ℝ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hw : ContDiff ℝ ∞ w)
    (hpa : Function.Periodic a 1) (hpw : Function.Periodic w 1) :
    (∫ x in (0:ℝ)..1, w x*a x*deriv w x) =
      -(1/2:ℂ)*(∫ x in (0:ℝ)..1, deriv a x*(w x)^2) := by
  have hp2 : Function.Periodic (fun x => (w x)^2) 1 := fun x => congrArg (fun z : ℂ => z^2) (hpw x)
  have h := integral_deriv_mul_periodic a (fun x => (w x)^2) ha (hw.pow 2) hpa hp2
  have hd : deriv (fun x => (w x)^2) = fun x => 2*w x*deriv w x := by
    funext x
    change deriv (w^2) x = 2*w x*deriv w x
    convert ((hw.differentiable (by simp) x).hasDerivAt.pow 2).deriv using 1
    ring
  rw [hd] at h
  have he : (fun x => a x*(2*w x*deriv w x)) = fun x => 2*(w x*a x*deriv w x) := by
    funext x
    ring
  rw [he,intervalIntegral.integral_const_mul] at h
  linear_combination (1/2:ℂ)*h

/-- A general real third-order transport field has the exact periodic
bilinear energy coefficient b-a_x/2. The identity itself is complex bilinear. -/
theorem integral_third_order_transport_energy (w a b : ℝ → ℂ)
    (hw : ContDiff ℝ ∞ w) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpw : Function.Periodic w 1) (hpa : Function.Periodic a 1) :
    (∫ x in (0:ℝ)..1, w x*(-deriv (deriv (deriv w)) x+a x*deriv w x+b x*w x)) =
      ∫ x in (0:ℝ)..1, (b x-(1/2:ℂ)*deriv a x)*(w x)^2 := by
  have hw1 := (contDiff_infty_iff_deriv.mp hw).2
  have hw2 := (contDiff_infty_iff_deriv.mp hw1).2
  have hw3 := (contDiff_infty_iff_deriv.mp hw2).2
  have ha1 := (contDiff_infty_iff_deriv.mp ha).2
  have hl := (hw.continuous.mul hw3.continuous).intervalIntegrable (μ := volume) 0 1
  have ht := ((hw.continuous.mul ha.continuous).mul hw1.continuous).intervalIntegrable (μ := volume) 0 1
  have hz := (hb.continuous.mul (hw.continuous.pow 2)).intervalIntegrable (μ := volume) 0 1
  have hc := (ha1.continuous.mul (hw.continuous.pow 2)).intervalIntegrable (μ := volume) 0 1
  have he : (fun x => w x*(-deriv (deriv (deriv w)) x+a x*deriv w x+b x*w x)) =
      fun x => -(w x*deriv (deriv (deriv w)) x)+w x*a x*deriv w x+b x*(w x)^2 := by
    funext x
    ring
  have he' : (fun x => (b x-(1/2:ℂ)*deriv a x)*(w x)^2) =
      fun x => b x*(w x)^2-(1/2:ℂ)*(deriv a x*(w x)^2) := by
    funext x
    ring
  rw [he,intervalIntegral.integral_add
    (f := fun x => -(w x*deriv (deriv (deriv w)) x)+w x*a x*deriv w x)
    (g := fun x => b x*(w x)^2) (hl.neg.add ht) hz,
    intervalIntegral.integral_add (f := fun x => -(w x*deriv (deriv (deriv w)) x))
      (g := fun x => w x*a x*deriv w x) hl.neg ht,intervalIntegral.integral_neg,
    integral_mul_deriv3_periodic_zero w hw hpw,
    integral_weighted_mul_deriv_periodic a w ha hw hpa hpw,he',
    intervalIntegral.integral_sub (f := fun x => b x*(w x)^2)
      (g := fun x => (1/2:ℂ)*(deriv a x*(w x)^2)) hz (hc.const_mul _),intervalIntegral.integral_const_mul]
  ring

end NLS.MKdV
