import NLS.MKdV.ClassicalDifferenceEnergy

/-! The physical KdV difference energy. Periodic integration by parts
leaves the coefficient 6v_x - 3u_x and gives a bound of 18R. -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory NLS.ZakharovShabat
open scoped ContDiff ComplexConjugate
namespace NLS.KdV
open NLS.MKdV

def scalarClassicalKdVField (u : ℝ → ℂ) (x : ℝ) : ℂ :=
  -deriv (deriv (deriv u)) x+6*u x*deriv u x

def classicalKdVDifferenceCoefficient (u v : ℝ → ℂ) (x : ℝ) : ℂ :=
  6*deriv v x-3*deriv u x

theorem periodic_scalarClassicalKdVField (u : ℝ → ℂ)
    (hp : Function.Periodic u 1) : Function.Periodic (scalarClassicalKdVField u) 1 := by
  intro x
  simp only [scalarClassicalKdVField,hp x,
    periodic_deriv_of_periodic u 1 hp x,
    periodic_deriv_of_periodic (deriv (deriv u)) 1
      (periodic_deriv_of_periodic (deriv u) 1 (periodic_deriv_of_periodic u 1 hp)) x]

theorem scalarClassicalKdVField_sub (u v : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (x : ℝ) :
    scalarClassicalKdVField u x-scalarClassicalKdVField v x =
      -deriv (deriv (deriv (fun y => u y-v y))) x+
        (6*u x)*deriv (fun y => u y-v y) x+
        (6*deriv v x)*(u x-v x) := by
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
  unfold scalarClassicalKdVField
  ring

theorem integral_scalarClassicalKdV_difference (u v : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hpu : Function.Periodic u 1) (hpv : Function.Periodic v 1)
    (hru : ∀ x, (u x).im = 0) (hrv : ∀ x, (v x).im = 0) :
    (∫ x in (0:ℝ)..1, conj (u x-v x)*
      (scalarClassicalKdVField u x-scalarClassicalKdVField v x)) =
    ∫ x in (0:ℝ)..1, classicalKdVDifferenceCoefficient u v x*(u x-v x)^2 := by
  let w := fun x => u x-v x
  let a := fun x => 6*u x
  let b := fun x => 6*deriv v x
  have hw : ContDiff ℝ ∞ w := hu.sub hv
  have ha : ContDiff ℝ ∞ a := contDiff_const.mul hu
  have hb : ContDiff ℝ ∞ b := contDiff_const.mul (contDiff_infty_iff_deriv.mp hv).2
  have hpa : Function.Periodic a 1 := by intro x; dsimp only [a]; rw [hpu x]
  have had (x : ℝ) : deriv a x = 6*deriv u x := by
    exact (((contDiff_infty_iff_deriv.mp hu).1 x).hasDerivAt.const_mul 6).deriv
  calc
    _ = ∫ x in (0:ℝ)..1, w x*(-deriv (deriv (deriv w)) x+a x*deriv w x+b x*w x) := by
      apply intervalIntegral.integral_congr
      intro x _
      have hr : conj (u x-v x) = u x-v x := by
        apply Complex.ext <;> simp [hru x,hrv x]
      change conj (u x-v x)*(scalarClassicalKdVField u x-scalarClassicalKdVField v x) =
        w x*(-deriv (deriv (deriv w)) x+a x*deriv w x+b x*w x)
      rw [hr,scalarClassicalKdVField_sub u v hu hv]
    _ = ∫ x in (0:ℝ)..1, (b x-(1/2:ℂ)*deriv a x)*(w x)^2 :=
      integral_third_order_transport_energy w a b hw ha hb (hpu.sub hpv) hpa
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro x _
      change (b x-(1/2:ℂ)*deriv a x)*(w x)^2 = classicalKdVDifferenceCoefficient u v x*(u x-v x)^2
      rw [had]
      dsimp only [w,b,classicalKdVDifferenceCoefficient]
      ring

theorem norm_classicalKdVDifferenceCoefficient_le (u v : ℝ → ℂ) (x R : ℝ)
    (hdu : ‖deriv u x‖ ≤ R) (hdv : ‖deriv v x‖ ≤ R) :
    ‖classicalKdVDifferenceCoefficient u v x‖ ≤ 9*R := by
  unfold classicalKdVDifferenceCoefficient
  calc
    _ ≤ ‖(6:ℂ)*deriv v x‖+‖(3:ℂ)*deriv u x‖ := norm_sub_le _ _
    _ = 6*‖deriv v x‖+3*‖deriv u x‖ := by simp only [norm_mul, norm_ofNat]
    _ ≤ 6*R+3*R := by gcongr
    _ = 9*R := by ring

/-- The exact physical difference-energy derivative is bounded by 18R
times the original unit-period squared L² distance. -/
theorem abs_scalarClassicalKdV_difference_energy_le (u v : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hpu : Function.Periodic u 1) (hpv : Function.Periodic v 1)
    (hru : ∀ x, (u x).im = 0) (hrv : ∀ x, (v x).im = 0)
    (R : ℝ)
    (hduR : ∀ x, ‖deriv u x‖ ≤ R) (hdvR : ∀ x, ‖deriv v x‖ ≤ R) :
    |2*(∫ x in (0:ℝ)..1, conj (u x-v x)*
      (scalarClassicalKdVField u x-scalarClassicalKdVField v x)).re| ≤
      18*R*(∫ x in (0:ℝ)..1, ‖u x-v x‖^2) := by
  rw [integral_scalarClassicalKdV_difference u v hu hv hpu hpv hru hrv]
  let f := fun x => classicalKdVDifferenceCoefficient u v x*(u x-v x)^2
  have hb (x : ℝ) : ‖f x‖ ≤ 9*R*‖u x-v x‖^2 := by
    rw [norm_mul,norm_pow]
    exact mul_le_mul_of_nonneg_right
      (norm_classicalKdVDifferenceCoefficient_le u v x R (hduR x) (hdvR x)) (sq_nonneg _)
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (by norm_num : (0:ℝ) ≤ 1)
    (Filter.Eventually.of_forall (fun x _ => hb x))
    ((continuous_const.mul ((hu.continuous.sub hv.continuous).norm.pow 2)).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at hi
  calc
    _ = 2*|(∫ x in (0:ℝ)..1, f x).re| := by rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ) < 2)]
    _ ≤ 2*‖∫ x in (0:ℝ)..1, f x‖ := mul_le_mul_of_nonneg_left (abs_re_le_norm _) (by norm_num)
    _ ≤ 2*(9*R*(∫ x in (0:ℝ)..1, ‖u x-v x‖^2)) := mul_le_mul_of_nonneg_left hi (by norm_num)
    _ = _ := by ring

end NLS.KdV
