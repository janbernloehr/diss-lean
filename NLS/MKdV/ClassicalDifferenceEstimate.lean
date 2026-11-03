import NLS.MKdV.ClassicalDifferenceEnergy

/-! # The physical periodic mKdV difference-energy bound

For real fields, periodic integration by parts removes the full third-order
and translation contributions. The remaining coefficient is bounded by the
uniform norms of the two fields and their first spatial derivatives.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory NLS.ZakharovShabat
open scoped ContDiff ComplexConjugate
namespace NLS.MKdV

def classicalMKdVDifferenceCoefficient (u v : ℝ → ℂ) (x : ℝ) : ℂ :=
  6*(u x+v x)*deriv v x-6*u x*deriv u x

theorem periodic_scalarClassicalMKdVField (M : ℂ) (u : ℝ → ℂ)
    (hp : Function.Periodic u 1) : Function.Periodic (scalarClassicalMKdVField M u) 1 := by
  intro x
  simp only [scalarClassicalMKdVField,hp x,
    periodic_deriv_of_periodic u 1 hp x,
    periodic_deriv_of_periodic (deriv (deriv u)) 1
      (periodic_deriv_of_periodic (deriv u) 1 (periodic_deriv_of_periodic u 1 hp)) x]

theorem scalarClassicalMKdVField_sub (M : ℂ) (u v : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (x : ℝ) :
    scalarClassicalMKdVField M u x-scalarClassicalMKdVField M v x =
      -deriv (deriv (deriv (fun y => u y-v y))) x+
        (6*((u x)^2-M))*deriv (fun y => u y-v y) x+
        (6*(u x+v x)*deriv v x)*(u x-v x) := by
  have hu1 := (contDiff_infty_iff_deriv.mp hu).2
  have hu2 := (contDiff_infty_iff_deriv.mp hu1).2
  have hv1 := (contDiff_infty_iff_deriv.mp hv).2
  have hv2 := (contDiff_infty_iff_deriv.mp hv1).2
  have h1 : deriv (fun y => u y-v y) = fun y => deriv u y-deriv v y := by
    funext y
    exact deriv_fun_sub ((contDiff_infty_iff_deriv.mp hu).1 y) ((contDiff_infty_iff_deriv.mp hv).1 y)
  have h2 : deriv (deriv (fun y => u y-v y)) = fun y => deriv (deriv u) y-deriv (deriv v) y := by
    rw [h1]
    funext y
    exact deriv_fun_sub ((contDiff_infty_iff_deriv.mp hu1).1 y) ((contDiff_infty_iff_deriv.mp hv1).1 y)
  have h3 : deriv (deriv (deriv (fun y => u y-v y))) =
      fun y => deriv (deriv (deriv u)) y-deriv (deriv (deriv v)) y := by
    rw [h2]
    funext y
    exact deriv_fun_sub ((contDiff_infty_iff_deriv.mp hu2).1 y) ((contDiff_infty_iff_deriv.mp hv2).1 y)
  rw [h3,h1]
  unfold scalarClassicalMKdVField
  ring

theorem integral_scalarClassicalMKdV_difference (M : ℂ) (u v : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hpu : Function.Periodic u 1) (hpv : Function.Periodic v 1)
    (hru : ∀ x, (u x).im = 0) (hrv : ∀ x, (v x).im = 0) :
    (∫ x in (0:ℝ)..1, conj (u x-v x)*
      (scalarClassicalMKdVField M u x-scalarClassicalMKdVField M v x)) =
    ∫ x in (0:ℝ)..1, classicalMKdVDifferenceCoefficient u v x*(u x-v x)^2 := by
  let w := fun x => u x-v x
  let a := fun x => 6*((u x)^2-M)
  let b := fun x => 6*(u x+v x)*deriv v x
  have hw : ContDiff ℝ ∞ w := hu.sub hv
  have ha : ContDiff ℝ ∞ a := contDiff_const.mul ((hu.pow 2).sub contDiff_const)
  have hb : ContDiff ℝ ∞ b := (contDiff_const.mul (hu.add hv)).mul (contDiff_infty_iff_deriv.mp hv).2
  have hpa : Function.Periodic a 1 := by intro x; dsimp only [a]; rw [hpu x]
  have had (x : ℝ) : deriv a x = 12*u x*deriv u x := by
    have h := ((((contDiff_infty_iff_deriv.mp hu).1 x).hasDerivAt.pow 2).sub_const M).const_mul 6
    change deriv (fun y => 6*((u^2) y-M)) x = _
    convert h.deriv using 1
    ring
  calc
    _ = ∫ x in (0:ℝ)..1, w x*(-deriv (deriv (deriv w)) x+a x*deriv w x+b x*w x) := by
      apply intervalIntegral.integral_congr
      intro x _
      have hr : conj (u x-v x) = u x-v x := by
        apply Complex.ext <;> simp [hru x,hrv x]
      change conj (u x-v x)*(scalarClassicalMKdVField M u x-scalarClassicalMKdVField M v x) =
        w x*(-deriv (deriv (deriv w)) x+a x*deriv w x+b x*w x)
      rw [hr,scalarClassicalMKdVField_sub M u v hu hv]
    _ = ∫ x in (0:ℝ)..1, (b x-(1/2:ℂ)*deriv a x)*(w x)^2 :=
      integral_third_order_transport_energy w a b hw ha hb (hpu.sub hpv) hpa
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x _
      change (b x-(1/2:ℂ)*deriv a x)*(w x)^2 = classicalMKdVDifferenceCoefficient u v x*(u x-v x)^2
      rw [had]
      dsimp only [w,b,classicalMKdVDifferenceCoefficient]
      ring

theorem norm_classicalMKdVDifferenceCoefficient_le (u v : ℝ → ℂ) (x R : ℝ) (hR : 0 ≤ R)
    (hu : ‖u x‖ ≤ R) (hv : ‖v x‖ ≤ R) (hdu : ‖deriv u x‖ ≤ R) (hdv : ‖deriv v x‖ ≤ R) :
    ‖classicalMKdVDifferenceCoefficient u v x‖ ≤ 18*R^2 := by
  have he : classicalMKdVDifferenceCoefficient u v x = 6*((u x+v x)*deriv v x-u x*deriv u x) := by
    unfold classicalMKdVDifferenceCoefficient
    ring
  rw [he,norm_mul]
  norm_num only [norm_ofNat]
  calc
    _ ≤ 6*(‖(u x+v x)*deriv v x‖+‖u x*deriv u x‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ = 6*(‖u x+v x‖*‖deriv v x‖+‖u x‖*‖deriv u x‖) := by rw [norm_mul,norm_mul]
    _ ≤ 6*((R+R)*R+R*R) := by
      gcongr
      exact (norm_add_le _ _).trans (add_le_add hu hv)
    _ = 18*R^2 := by ring

/-- The exact physical difference-energy derivative is bounded by 36R²
times the original unit-period squared L² distance, independently of M. -/
theorem abs_scalarClassicalMKdV_difference_energy_le (M : ℂ) (u v : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hpu : Function.Periodic u 1) (hpv : Function.Periodic v 1)
    (hru : ∀ x, (u x).im = 0) (hrv : ∀ x, (v x).im = 0)
    (R : ℝ) (hR : 0 ≤ R) (huR : ∀ x, ‖u x‖ ≤ R) (hvR : ∀ x, ‖v x‖ ≤ R)
    (hduR : ∀ x, ‖deriv u x‖ ≤ R) (hdvR : ∀ x, ‖deriv v x‖ ≤ R) :
    |2*(∫ x in (0:ℝ)..1, conj (u x-v x)*
      (scalarClassicalMKdVField M u x-scalarClassicalMKdVField M v x)).re| ≤
      36*R^2*(∫ x in (0:ℝ)..1, ‖u x-v x‖^2) := by
  rw [integral_scalarClassicalMKdV_difference M u v hu hv hpu hpv hru hrv]
  let f := fun x => classicalMKdVDifferenceCoefficient u v x*(u x-v x)^2
  have hb (x : ℝ) : ‖f x‖ ≤ 18*R^2*‖u x-v x‖^2 := by
    rw [norm_mul,norm_pow]
    exact mul_le_mul_of_nonneg_right
      (norm_classicalMKdVDifferenceCoefficient_le u v x R hR (huR x) (hvR x) (hduR x) (hdvR x)) (sq_nonneg _)
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    (Filter.Eventually.of_forall (fun x _ => hb x))
    ((continuous_const.mul ((hu.continuous.sub hv.continuous).norm.pow 2)).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at hi
  calc
    _ = 2*|(∫ x in (0:ℝ)..1, f x).re| := by rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    _ ≤ 2*‖∫ x in (0:ℝ)..1, f x‖ := mul_le_mul_of_nonneg_left (abs_re_le_norm _) (by norm_num)
    _ ≤ 2*(18*R^2*(∫ x in (0:ℝ)..1, ‖u x-v x‖^2)) := mul_le_mul_of_nonneg_left hi (by norm_num)
    _ = _ := by ring

end NLS.MKdV
