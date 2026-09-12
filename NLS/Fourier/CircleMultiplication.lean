import NLS.Fourier.CirclePrimitive

/-!
# Physical multiplication by a continuous circle function

A continuous factor multiplies an arbitrary `L²` function, with its actual
almost-everywhere product and the uniform-norm bound. This bounded bilinear map
allows uniformly convergent Fourier series to act on nonsmooth potentials.
-/

noncomputable section
open MeasureTheory
namespace NLS.Fourier

private theorem memLp_continuous_mul (f : C(AddCircle (2 : ℝ), ℂ)) (g : CircleL2) :
    MemLp (fun x => f x * g x) 2 AddCircle.haarAddCircle := by
  apply (Lp.memLp g).of_le_mul (c := ‖f‖) (f.continuous.aestronglyMeasurable.mul (Lp.memLp g).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm x) (norm_nonneg _)

/-- The actual pointwise product, considered as an `L²` equivalence class. -/
def circleMul (f : C(AddCircle (2 : ℝ), ℂ)) (g : CircleL2) : CircleL2 :=
  (memLp_continuous_mul f g).toLp (fun x => f x * g x)

theorem coeFn_circleMul (f : C(AddCircle (2 : ℝ), ℂ)) (g : CircleL2) :
    circleMul f g =ᵐ[AddCircle.haarAddCircle] (fun x => f x * g x) :=
  (memLp_continuous_mul f g).coeFn_toLp

theorem norm_circleMul_le (f : C(AddCircle (2 : ℝ), ℂ)) (g : CircleL2) :
    ‖circleMul f g‖ ≤ ‖f‖ * ‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coeFn_circleMul f g] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm x) (norm_nonneg _)

private theorem circleMul_add_left (f h : C(AddCircle (2 : ℝ), ℂ)) (g : CircleL2) :
    circleMul (f + h) g = circleMul f g + circleMul h g := by
  apply Lp.ext
  filter_upwards [coeFn_circleMul (f + h) g, coeFn_circleMul f g, coeFn_circleMul h g,
    Lp.coeFn_add (circleMul f g) (circleMul h g)] with x hx hf hh ha
  simp only [hx, ha, Pi.add_apply, hf, hh, ContinuousMap.add_apply, add_mul]

private theorem circleMul_add_right (f : C(AddCircle (2 : ℝ), ℂ)) (g h : CircleL2) :
    circleMul f (g + h) = circleMul f g + circleMul f h := by
  apply Lp.ext
  filter_upwards [coeFn_circleMul f (g + h), coeFn_circleMul f g, coeFn_circleMul f h,
    Lp.coeFn_add g h, Lp.coeFn_add (circleMul f g) (circleMul f h)] with x hx hg hh ha hb
  simp only [hx, ha, hb, Pi.add_apply, hg, hh, mul_add]

private theorem circleMul_smul_left (c : ℂ) (f : C(AddCircle (2 : ℝ), ℂ)) (g : CircleL2) :
    circleMul (c • f) g = c • circleMul f g := by
  apply Lp.ext
  filter_upwards [coeFn_circleMul (c • f) g, coeFn_circleMul f g,
    Lp.coeFn_smul c (circleMul f g)] with x hx hf hc
  simp only [hx, hc, Pi.smul_apply, hf, ContinuousMap.smul_apply, smul_eq_mul, mul_assoc]

private theorem circleMul_smul_right (c : ℂ) (f : C(AddCircle (2 : ℝ), ℂ)) (g : CircleL2) :
    circleMul f (c • g) = c • circleMul f g := by
  apply Lp.ext
  filter_upwards [coeFn_circleMul f (c • g), coeFn_circleMul f g,
    Lp.coeFn_smul c g, Lp.coeFn_smul c (circleMul f g)] with x hx hf hc hd
  simp only [hx, hd, hc, Pi.smul_apply, hf, smul_eq_mul, mul_left_comm]

/-- Multiplication is jointly bounded and complex bilinear. -/
def circleMulCLM : C(AddCircle (2 : ℝ), ℂ) →L[ℂ] CircleL2 →L[ℂ] CircleL2 :=
  (LinearMap.mk₂ ℂ circleMul circleMul_add_left circleMul_smul_left
    circleMul_add_right circleMul_smul_right).mkContinuous₂ 1
    (fun f g => by simpa only [one_mul, LinearMap.mk₂_apply] using norm_circleMul_le f g)

@[simp] theorem circleMulCLM_apply (f : C(AddCircle (2 : ℝ), ℂ)) (g : CircleL2) :
    circleMulCLM f g = circleMul f g := rfl

/-- Multiplication by one preserves arbitrary `L²` data. -/
@[simp] theorem circleMul_one (g : CircleL2) : circleMul 1 g = g := by
  apply Lp.ext
  filter_upwards [coeFn_circleMul 1 g] with x hx
  simpa using hx

/-- The circle product has the expected physical meaning on a full real period. -/
theorem circlePullback_circleMul (f : C(AddCircle (2 : ℝ), ℂ)) (g : CircleL2) :
    circlePullback (circleMul f g) =ᵐ[volume.restrict (Set.Ioc 0 2)]
      (fun x : ℝ => f (x : AddCircle (2 : ℝ)) * circlePullback g x) :=
  circle_ae_pullback (coeFn_circleMul f g)

end NLS.Fourier
