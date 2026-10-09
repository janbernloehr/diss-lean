import NLS.ZakharovShabat.PhysicalL2IntegralPairing
import NLS.ZakharovShabat.L2SolutionExtension

/-! # The original Volterra equation for arbitrary physical L2 potentials

Pass the actual coefficient integral to the uniform solution limit using
joint continuity in the physical L2 potential and the continuous curve.
-/
noncomputable section
open Set Complex MeasureTheory Filter Topology
open scoped BoundedContinuousFunction
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

private def boundedFirst (w : Curve (ℂ × ℂ)) : ℝ →ᵇ ℂ :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).compLeftContinuousBounded ℝ (curveBoundedExtension _ w)

private def boundedSecond (w : Curve (ℂ × ℂ)) : ℝ →ᵇ ℂ :=
  (ContinuousLinearMap.snd ℂ ℂ ℂ).compLeftContinuousBounded ℝ (curveBoundedExtension _ w)

/-- The actual coefficient integral with an original physical L2 representative. -/
def l2ODEIntegral (u : IntervalPairL2) (z : ℂ) (w : Curve (ℂ × ℂ)) (t : Icc (0:ℝ) 1) : ℂ × ℂ :=
  ∫ s in (0:ℝ)..t.val, classicalODECoefficient (intervalL2Representative u s) z (extend w s)

/-- The original coefficient times any continuous curve is integrable. -/
theorem intervalIntegrable_l2ODECoefficient (u : IntervalPairL2) (z : ℂ)
    (w : Curve (ℂ × ℂ)) (t : Icc (0:ℝ) 1) :
    IntervalIntegrable (fun s => classicalODECoefficient (intervalL2Representative u s) z (extend w s))
      volume 0 t.val := by
  have h₁ := ((continuous_extend w).fst.intervalIntegrable (μ := volume) 0 t.val).const_mul (-I*z)
  have h₂ := ((continuous_extend w).snd.intervalIntegrable (μ := volume) 0 t.val).const_mul (I*z)
  have hp₁ := (intervalIntegrable_intervalL2_mul u.ofLp.1 (boundedSecond w) t).const_mul I
  have hp₂ := (intervalIntegrable_intervalL2_mul u.ofLp.2 (boundedFirst w) t).const_mul (-I)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le t.property.1).mpr
  simpa only [IntegrableOn,classicalODECoefficient_apply,intervalL2Representative,boundedFirst,boundedSecond,
    ContinuousLinearMap.compLeftContinuousBounded_apply,curveBoundedExtension_apply,
    ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',mul_assoc] using
    ((h₁.add hp₁).1.prodMk (hp₂.add h₂).1)

/-- Coordinate formula for the original integral, including both spectral signs. -/
private theorem l2ODEIntegral_eq (u : IntervalPairL2) (z : ℂ) (w : Curve (ℂ × ℂ)) (t : Icc (0:ℝ) 1) :
    l2ODEIntegral u z w t =
      (-I*z*(∫ s in (0:ℝ)..t.val, boundedFirst w s)+
        I*(∫ s in (0:ℝ)..t.val, u.ofLp.1 s*boundedSecond w s),
       -I*(∫ s in (0:ℝ)..t.val, u.ofLp.2 s*boundedFirst w s)+
        I*z*(∫ s in (0:ℝ)..t.val, boundedSecond w s)) := by
  have h₁ := ((continuous_extend w).fst.intervalIntegrable (μ := volume) 0 t.val).const_mul (-I*z)
  have h₂ := ((continuous_extend w).snd.intervalIntegrable (μ := volume) 0 t.val).const_mul (I*z)
  have hp₁ := (intervalIntegrable_intervalL2_mul u.ofLp.1 (boundedSecond w) t).const_mul I
  have hp₂ := (intervalIntegrable_intervalL2_mul u.ofLp.2 (boundedFirst w) t).const_mul (-I)
  simp only [boundedFirst,boundedSecond,ContinuousLinearMap.compLeftContinuousBounded_apply,
    curveBoundedExtension_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd'] at hp₁ hp₂ ⊢
  simp_rw [← mul_assoc] at hp₁ hp₂
  simp only [l2ODEIntegral,classicalODECoefficient_apply,intervalL2Representative]
  simp_rw [intervalIntegral.integral_of_le t.property.1]
  rw [integral_pair (h₁.add hp₁).1 (hp₂.add h₂).1,
    integral_add h₁.1 hp₁.1,integral_add hp₂.1 h₂.1]
  simp only [mul_assoc,integral_const_mul]

/-- Joint continuity in the physical L2 class and uniform curve, at each time. -/
theorem continuous_l2ODEIntegral (z : ℂ) (t : Icc (0:ℝ) 1) :
    Continuous (fun p : IntervalPairL2 × Curve (ℂ × ℂ) => l2ODEIntegral p.1 z p.2 t) := by
  have hf : Continuous (fun p : IntervalPairL2 × Curve (ℂ × ℂ) => boundedFirst p.2) :=
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).compLeftContinuousBounded ℝ).continuous.comp
      ((curveBoundedExtension _).continuous.comp continuous_snd)
  have hg : Continuous (fun p : IntervalPairL2 × Curve (ℂ × ℂ) => boundedSecond p.2) :=
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).compLeftContinuousBounded ℝ).continuous.comp
      ((curveBoundedExtension _).continuous.comp continuous_snd)
  have hu := (WithLp.prodContinuousLinearEquiv 2 ℂ IntervalL2 IntervalL2).continuous.comp
    (continuous_fst : Continuous (fun p : IntervalPairL2 × Curve (ℂ × ℂ) => p.1))
  have h₁ := (continuous_bounded_intervalIntegral t).comp hf
  have h₂ := (continuous_bounded_intervalIntegral t).comp hg
  have hp₁ := (continuous_intervalL2_integral_mul t).comp (hu.fst.prodMk hg)
  have hp₂ := (continuous_intervalL2_integral_mul t).comp (hu.snd.prodMk hf)
  simp_rw [l2ODEIntegral_eq]
  exact ((continuous_const.mul h₁).add (continuous_const.mul hp₁)).prodMk
    ((continuous_const.mul hp₂).add (continuous_const.mul h₂))

/-- The original integral agrees exactly with the classical coefficient integral. -/
theorem l2ODEIntegral_of_continuous (φ : Curve (ℂ × ℂ)) (z : ℂ) (w : Curve (ℂ × ℂ))
    (t : Icc (0:ℝ) 1) :
    l2ODEIntegral (continuousPotentialL2Class φ) z w t =
      ∫ s in (0:ℝ)..t.val, classicalODECoefficient (extend φ s) z (extend w s) := by
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le t.property.1]
  filter_upwards [ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right t.property.2) (le_refl volume))
    (continuousPotentialL2Class_representative φ)] with s hs
  rw [hs]

/-- The classical curve satisfies the same representative-based integral equation. -/
theorem classicalSolutionCurve_eq_l2ODEIntegral (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0:ℝ) 1) :
    classicalSolutionCurve φ z v t = v+l2ODEIntegral (continuousPotentialL2Class φ) z
      (classicalSolutionCurve φ z v) t := by
  rw [l2ODEIntegral_of_continuous]
  exact solutionCurve_eq (classicalODECurve φ z) v t

/-- The uniform extension solves the original Volterra equation for every physical L2 potential. -/
theorem l2SolutionCurve_eq_integral (u : IntervalPairL2) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0:ℝ) 1) :
    l2SolutionCurve u z v t = v+∫ s in (0:ℝ)..t.val,
      classicalODECoefficient (intervalL2Representative u s) z (extend (l2SolutionCurve u z v) s) := by
  let : NeBot (continuousPotentialL2Filter u) := continuousPotentialL2Filter_neBot u
  have hs := tendsto_classicalSolutionCurve_L2 u z v
  have hp : Tendsto continuousPotentialL2Class (continuousPotentialL2Filter u) (𝓝 u) := tendsto_comap
  have hl := (continuous_eval_const t).continuousAt.tendsto.comp hs
  have hr := (tendsto_const_nhds (x := v)).add
    ((continuous_l2ODEIntegral z t).continuousAt.tendsto.comp (hp.prodMk_nhds hs))
  have he : (fun φ => classicalSolutionCurve φ z v t) =
      (fun φ => v+l2ODEIntegral (continuousPotentialL2Class φ) z (classicalSolutionCurve φ z v) t) := by
    funext φ
    exact classicalSolutionCurve_eq_l2ODEIntegral φ z v t
  simp only [Function.comp_def] at hl hr
  rw [← he] at hr
  exact tendsto_nhds_unique hl hr

/-- Any original square-integrable representative gives the same actual coefficient integral. -/
theorem l2ODEIntegral_ofFunction (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (z : ℂ) (w : Curve (ℂ × ℂ))
    (t : Icc (0:ℝ) 1) :
    l2ODEIntegral (intervalL2OfFunction φ hφ) z w t =
      ∫ s in (0:ℝ)..t.val, classicalODECoefficient (φ s) z (extend w s) := by
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le t.property.1]
  filter_upwards [ae_mono (Measure.restrict_mono (Ioc_subset_Ioc_right t.property.2) (le_refl volume))
    (intervalL2Representative_ofFunction φ hφ)] with s hs
  rw [hs]

/-- The equation uses the original function, independently of changes on null sets. -/
theorem l2SolutionCurve_eq_integral_ofFunction (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0:ℝ) 1) :
    l2SolutionCurve (intervalL2OfFunction φ hφ) z v t = v+∫ s in (0:ℝ)..t.val,
      classicalODECoefficient (φ s) z (extend (l2SolutionCurve (intervalL2OfFunction φ hφ) z v) s) := by
  have h := l2SolutionCurve_eq_integral (intervalL2OfFunction φ hφ) z v t
  change _ = v+l2ODEIntegral (intervalL2OfFunction φ hφ) z _ t at h
  rwa [l2ODEIntegral_ofFunction] at h

end NLS.ZakharovShabat
