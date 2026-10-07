import NLS.ZakharovShabat.ClassicalNLSVectorField

/-! # The periodic NLS difference-energy estimate

The linear Schrödinger term contributes no real difference energy.
The cubic nonlinearity is Lipschitz on bounded complex discs, yielding
the quantitative energy bound used for classical uniqueness.
-/
noncomputable section
open Set Complex MeasureTheory
open scoped ContDiff ComplexConjugate
namespace NLS.ZakharovShabat

/-- The scalar defocusing cubic in the normalization of the physical NLS equation. -/
def classicalNLSCubic (z : ℂ) : ℂ := 2*z^2*conj z

/-- The cubic has Lipschitz constant `6 M²` on the closed disc of radius `M`. -/
theorem norm_classicalNLSCubic_sub_le (z w : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hz : ‖z‖ ≤ M) (hw : ‖w‖ ≤ M) :
    ‖classicalNLSCubic z-classicalNLSCubic w‖ ≤ 6*M^2*‖z-w‖ := by
  have he : classicalNLSCubic z-classicalNLSCubic w =
      2*((z-w)*(z+w)*conj z+w^2*conj (z-w)) := by
    simp only [classicalNLSCubic,map_sub]
    ring
  rw [he,norm_mul]
  norm_num only [norm_ofNat]
  calc
    _ ≤ 2*(‖(z-w)*(z+w)*conj z‖+‖w^2*conj (z-w)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = 2*(‖z-w‖*‖z+w‖*‖z‖+‖w‖^2*‖z-w‖) := by
      simp only [norm_mul,norm_pow,norm_conj]
    _ ≤ 2*(‖z-w‖*(M+M)*M+M^2*‖z-w‖) := by
      gcongr
      exact (norm_add_le z w).trans (add_le_add hz hw)
    _ = 6*M^2*‖z-w‖ := by ring

/-- The actual scalar NLS velocity with the Hamiltonian time orientation. -/
def scalarClassicalNLSVectorField (u : ℝ → ℂ) (x : ℝ) : ℂ :=
  I*deriv (deriv u) x-I*classicalNLSCubic (u x)

/-- This scalar velocity is the first component of the existing physical real-pair field. -/
theorem scalarClassicalNLSVectorField_eq (u : ℝ → ℂ) :
    scalarClassicalNLSVectorField u = (classicalNLSVectorField u (fun x => conj (u x))).1 := by
  funext x
  simp only [scalarClassicalNLSVectorField,classicalNLSVectorField,classicalNLSEnergyGradient,classicalNLSCubic]
  ring

/-- The periodic second derivative has real pairing with its source. -/
theorem integral_conj_mul_deriv2_im_eq_zero (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hp : Function.Periodic u 1) :
    (∫ x in (0 : ℝ)..1, conj (u x)*deriv (deriv u) x).im = 0 := by
  have hd := (contDiff_infty_iff_deriv.mp hu).2
  have hc : ContDiff ℝ ∞ (fun x => conj (u x)) := conjCLE.contDiff.comp hu
  have hpc : Function.Periodic (fun x => conj (u x)) 1 := fun x => congrArg conj (hp x)
  have hpd := periodic_deriv_of_periodic u 1 hp
  have hi := integral_deriv_mul_periodic (fun x => conj (u x)) (deriv u) hc hd hpc hpd
  have he : (∫ x in (0 : ℝ)..1, conj (u x)*deriv (deriv u) x) =
      -(∫ x in (0 : ℝ)..1, conj (deriv u x)*deriv u x) := by
    have hdstar : deriv (fun x => conj (u x)) = fun x => conj (deriv u x) := deriv.star'
    rw [hdstar] at hi
    simpa only [neg_neg] using (congrArg Neg.neg hi).symm
  rw [he,neg_im,neg_eq_zero]
  have hint : IntervalIntegrable (fun x => conj (deriv u x)*deriv u x) volume 0 1 := (hd.continuous.star.mul hd.continuous).intervalIntegrable 0 1
  calc
    _ = ∫ x in (0 : ℝ)..1, (conj (deriv u x)*deriv u x).im :=
      (intervalIntegral.intervalIntegral_im hint).symm
    _ = 0 := by
      have heq : (fun x => (conj (deriv u x)*deriv u x).im) = fun _ => (0 : ℝ) := by
        funext x
        simp only [mul_im,conj_re,conj_im]
        ring
      rw [heq,intervalIntegral.integral_zero]

/-- The linear Schrödinger part contributes zero to the real difference pairing. -/
theorem integral_conj_mul_linearNLS_re_eq_zero (u : ℝ → ℂ) (hu : ContDiff ℝ ∞ u)
    (hp : Function.Periodic u 1) :
    (∫ x in (0 : ℝ)..1, conj (u x)*(I*deriv (deriv u) x)).re = 0 := by
  have he : (fun x => conj (u x)*(I*deriv (deriv u) x)) =
      (fun x => I*(conj (u x)*deriv (deriv u) x)) := by funext x; ring
  rw [he,intervalIntegral.integral_const_mul]
  simp only [mul_re,I_re,I_im,zero_mul,one_mul,zero_sub,
    integral_conj_mul_deriv2_im_eq_zero u hu hp,neg_zero]

/-- The difference of scalar fields separates into the skew linear part
and the actual cubic difference. -/
theorem scalarClassicalNLSVectorField_sub (u v : ℝ → ℂ)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (x : ℝ) :
    scalarClassicalNLSVectorField u x-scalarClassicalNLSVectorField v x =
      I*deriv (deriv (fun y => u y-v y)) x-I*(classicalNLSCubic (u x)-classicalNLSCubic (v x)) := by
  have hd : deriv (fun y => u y-v y) = fun y => deriv u y-deriv v y := by
    funext y
    exact deriv_fun_sub ((contDiff_infty_iff_deriv.mp hu).1 y) ((contDiff_infty_iff_deriv.mp hv).1 y)
  rw [hd,deriv_fun_sub ((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hu).2).1 x)
    ((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hv).2).1 x)]
  unfold scalarClassicalNLSVectorField
  ring

/-- Periodic integration by parts removes the full linear contribution
to the real difference-energy pairing. -/
theorem integral_scalarClassicalNLS_difference_re
    (u v : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hpu : Function.Periodic u 1) (hpv : Function.Periodic v 1) :
    (∫ x in (0 : ℝ)..1, conj (u x-v x)*
      (scalarClassicalNLSVectorField u x-scalarClassicalNLSVectorField v x)).re =
    (∫ x in (0 : ℝ)..1, conj (u x-v x)*(-I*(classicalNLSCubic (u x)-classicalNLSCubic (v x)))).re := by
  let d := fun x => u x-v x
  have hd : ContDiff ℝ ∞ d := hu.sub hv
  have hpd : Function.Periodic d 1 := hpu.sub hpv
  have hdd := (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hd).2).2
  have hc : Continuous (fun x => classicalNLSCubic (u x)-classicalNLSCubic (v x)) := by
    have huc := hu.continuous
    have hvc := hv.continuous
    unfold classicalNLSCubic
    fun_prop
  have hl : IntervalIntegrable (fun x => conj (d x)*(I*deriv (deriv d) x)) volume 0 1 := (hd.continuous.star.mul (continuous_const.mul hdd.continuous)).intervalIntegrable 0 1
  have hn : IntervalIntegrable (fun x => conj (d x)*(-I*(classicalNLSCubic (u x)-classicalNLSCubic (v x)))) volume 0 1 := (hd.continuous.star.mul (continuous_const.mul hc)).intervalIntegrable 0 1
  have he : (fun x => conj (u x-v x)*(scalarClassicalNLSVectorField u x-scalarClassicalNLSVectorField v x)) =
      (fun x => conj (d x)*(I*deriv (deriv d) x)+
        conj (d x)*(-I*(classicalNLSCubic (u x)-classicalNLSCubic (v x)))) := by
    funext x
    rw [scalarClassicalNLSVectorField_sub u v hu hv]
    change conj (d x)*(_-_) = _
    ring
  rw [he,intervalIntegral.integral_add hl hn,add_re,
    integral_conj_mul_linearNLS_re_eq_zero d hd hpd,zero_add]

/-- The real difference-energy derivative is bounded in absolute value
by `12 M²` times the squared L² distance, for bounded smooth periodic data. -/
theorem abs_scalarClassicalNLS_difference_energy_le
    (u v : ℝ → ℂ) (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hpu : Function.Periodic u 1) (hpv : Function.Periodic v 1)
    (M : ℝ) (hM : 0 ≤ M) (huM : ∀ x, ‖u x‖ ≤ M) (hvM : ∀ x, ‖v x‖ ≤ M) :
    |2*(∫ x in (0 : ℝ)..1, conj (u x-v x)*
      (scalarClassicalNLSVectorField u x-scalarClassicalNLSVectorField v x)).re| ≤
      12*M^2*(∫ x in (0 : ℝ)..1, ‖u x-v x‖^2) := by
  rw [integral_scalarClassicalNLS_difference_re u v hu hv hpu hpv]
  let f := fun x => conj (u x-v x)*(-I*(classicalNLSCubic (u x)-classicalNLSCubic (v x)))
  have hb (x : ℝ) : ‖f x‖ ≤ 6*M^2*‖u x-v x‖^2 := by
    calc
      _ = ‖u x-v x‖*‖classicalNLSCubic (u x)-classicalNLSCubic (v x)‖ := by
        simp only [f,norm_mul,norm_neg,norm_I,norm_conj,one_mul]
      _ ≤ ‖u x-v x‖*(6*M^2*‖u x-v x‖) :=
        mul_le_mul_of_nonneg_left (norm_classicalNLSCubic_sub_le _ _ M hM (huM x) (hvM x)) (norm_nonneg _)
      _ = _ := by ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (Filter.Eventually.of_forall (fun x _ => hb x))
    ((continuous_const.mul ((hu.continuous.sub hv.continuous).norm.pow 2)).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at hi
  calc
    _ = 2*|(∫ x in (0 : ℝ)..1, f x).re| := by rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2*‖∫ x in (0 : ℝ)..1, f x‖ := mul_le_mul_of_nonneg_left (abs_re_le_norm _) (by norm_num)
    _ ≤ 2*(6*M^2*(∫ x in (0 : ℝ)..1, ‖u x-v x‖^2)) := mul_le_mul_of_nonneg_left hi (by norm_num)
    _ = _ := by ring

end NLS.ZakharovShabat
