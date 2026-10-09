import NLS.ZakharovShabat.L2OscillatoryIntegral
import NLS.ZakharovShabat.ClassicalHermitianOperatorBound

/-! # The actual Hermitian first Born operator for physical L2 potentials

The operator is formed from the original oscillatory integrals. Its curve
in time depends continuously on the physical potential in the uniform norm.
-/
noncomputable section
open Set Complex MeasureTheory
open NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.ZakharovShabat

/-- The actual off-diagonal first Born operator, continuous up to both endpoints. -/
def l2HermitianFirstBornOperatorCurve (u : IntervalPairL2) (z : ℂ) :
    Curve (HermitianPair →L[ℂ] HermitianPair) where
  toFun t := hermitianColumns (0,-I*(l2OscillatoryCurve (I*z) u.ofLp.2 t))
    (I*(l2OscillatoryCurve (-I*z) u.ofLp.1 t),0)
  continuous_toFun := by
    have h : Continuous (fun t : Icc (0:ℝ) 1 =>
        (((0:ℂ),-I*(l2OscillatoryCurve (I*z) u.ofLp.2 t)),
          (I*(l2OscillatoryCurve (-I*z) u.ofLp.1 t),(0:ℂ)))) :=
      (continuous_const.prodMk (continuous_const.mul (l2OscillatoryCurve (I*z) u.ofLp.2).continuous)).prodMk
        ((continuous_const.mul (l2OscillatoryCurve (-I*z) u.ofLp.1).continuous).prodMk continuous_const)
    simpa only [Function.comp_def] using continuous_hermitianColumns.comp h

/-- Identification with the original oscillatory integral, not an error majorant. -/
theorem l2HermitianFirstBornOperatorCurve_apply (u : IntervalPairL2) (z : ℂ) (t : Icc (0:ℝ) 1) :
    l2HermitianFirstBornOperatorCurve u z t =
      hermitianColumns (0,-I*oscillatoryIntegral (I*z) t u.ofLp.2)
        (I*oscillatoryIntegral (-I*z) t u.ofLp.1,0) := by
  simp only [l2HermitianFirstBornOperatorCurve,ContinuousMap.coe_mk,l2OscillatoryCurve_apply]

/-- The original first Born matrix on the physical interval. -/
def l2FirstBornMatrix (u : IntervalPairL2) (z : ℂ) (t : Icc (0:ℝ) 1) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0,I*oscillatoryIntegral (-I*z) t u.ofLp.1;
     -I*oscillatoryIntegral (I*z) t u.ofLp.2,0]

theorem l2HermitianFirstBornOperatorCurve_eq_matrix (u : IntervalPairL2) (z : ℂ) (t : Icc (0:ℝ) 1) :
    l2HermitianFirstBornOperatorCurve u z t = classicalHermitianMatrixOperator (l2FirstBornMatrix u z t) := by
  rw [l2HermitianFirstBornOperatorCurve_apply]
  rfl

/-- L2 convergence gives uniform convergence of the actual first Born operator. -/
theorem continuous_l2HermitianFirstBornOperatorCurve (z : ℂ) :
    Continuous (fun u : IntervalPairL2 => l2HermitianFirstBornOperatorCurve u z) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  rw [Function.uncurry_def]
  have hu := (WithLp.prodContinuousLinearEquiv 2 ℂ IntervalL2 IntervalL2).continuous.comp
    (continuous_fst : Continuous (fun p : IntervalPairL2 × Icc (0:ℝ) 1 => p.1))
  have h₁ := continuous_eval.comp (((l2OscillatoryCurve (-I*z)).continuous.comp hu.fst).prodMk continuous_snd)
  have h₂ := continuous_eval.comp (((l2OscillatoryCurve (I*z)).continuous.comp hu.snd).prodMk continuous_snd)
  have hc : Continuous (fun p : IntervalPairL2 × Icc (0:ℝ) 1 =>
      (((0:ℂ),-I*l2OscillatoryCurve (I*z) p.1.ofLp.2 p.2),
        (I*l2OscillatoryCurve (-I*z) p.1.ofLp.1 p.2,(0:ℂ)))) :=
    (continuous_const.prodMk (continuous_const.mul h₂)).prodMk
      ((continuous_const.mul h₁).prodMk continuous_const)
  simpa only [Function.comp_def,Function.uncurry_def,l2HermitianFirstBornOperatorCurve,ContinuousMap.coe_mk]
    using continuous_hermitianColumns.comp hc

/-- Weighted genuine Hermitian operator norm, as a continuous real curve. -/
def l2NormalizedHermitianFirstBorn (u : IntervalPairL2) (z : ℂ) : Curve ℝ where
  toFun t := Real.exp (-(|z.im| *t.val))*‖l2HermitianFirstBornOperatorCurve u z t‖
  continuous_toFun := (by fun_prop : Continuous (fun t : Icc (0:ℝ) 1 => Real.exp (-(|z.im| *t.val)))).mul
    (l2HermitianFirstBornOperatorCurve u z).continuous.norm

/-- Continuity of the normalized Born curve in the uniform norm. -/
theorem continuous_l2NormalizedHermitianFirstBorn (z : ℂ) :
    Continuous (fun u : IntervalPairL2 => l2NormalizedHermitianFirstBorn u z) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  rw [Function.uncurry_def]
  have h := continuous_eval.comp
    (((continuous_l2HermitianFirstBornOperatorCurve z).comp continuous_fst).prodMk continuous_snd)
  exact (by fun_prop : Continuous (fun p : IntervalPairL2 × Icc (0:ℝ) 1 =>
    Real.exp (-(|z.im| *p.2.val)))).mul h.norm

/-- Exact Hermitian off-diagonal norm, with no dimension-dependent factor. -/
theorem l2NormalizedHermitianFirstBorn_eq (u : IntervalPairL2) (z : ℂ) (t : Icc (0:ℝ) 1) :
    l2NormalizedHermitianFirstBorn u z t = Real.exp (-(|z.im| *t.val))*
      max ‖oscillatoryIntegral (-I*z) t u.ofLp.1‖ ‖oscillatoryIntegral (I*z) t u.ofLp.2‖ := by
  change Real.exp _ * ‖l2HermitianFirstBornOperatorCurve u z t‖ = _
  rw [l2HermitianFirstBornOperatorCurve_apply,norm_hermitianColumns_offDiagonal]
  simp only [norm_mul,norm_neg,norm_I,one_mul]

/-- Exact classical recovery of the operator, before taking any norm. -/
theorem l2HermitianFirstBornOperatorCurve_of_continuous (φ : Curve (ℂ × ℂ)) (z : ℂ)
    (t : Icc (0:ℝ) 1) :
    l2HermitianFirstBornOperatorCurve (continuousPotentialL2Class φ) z t =
      classicalHermitianFirstBornOperator φ z t := by
  have h₁ : l2OscillatoryCurve (-I*z) (continuousPotentialL2Class φ).ofLp.1 t =
      oscillatoryIntegral (-I*z) t (fun s => (extend φ s).1) :=
    l2OscillatoryCurve_apply_ofFunction _ _ (memLp_extend_continuousPotential φ).fst t
  have h₂ : l2OscillatoryCurve (I*z) (continuousPotentialL2Class φ).ofLp.2 t =
      oscillatoryIntegral (I*z) t (fun s => (extend φ s).2) :=
    l2OscillatoryCurve_apply_ofFunction _ _ (memLp_extend_continuousPotential φ).snd t
  simp only [l2HermitianFirstBornOperatorCurve,ContinuousMap.coe_mk,h₁,h₂,
    classicalHermitianFirstBornOperator,classicalFirstBornVector,mul_zero,mul_one]

/-- The normalization also recovers the exact continuous-potential definition. -/
theorem l2NormalizedHermitianFirstBorn_of_continuous (φ : Curve (ℂ × ℂ)) (z : ℂ)
    (t : Icc (0:ℝ) 1) :
    l2NormalizedHermitianFirstBorn (continuousPotentialL2Class φ) z t =
      classicalNormalizedHermitianFirstBorn φ z t := by
  change Real.exp _ * ‖l2HermitianFirstBornOperatorCurve (continuousPotentialL2Class φ) z t‖ = _
  rw [l2HermitianFirstBornOperatorCurve_of_continuous]
  rfl

/-- The actual Born operator uses any original square-integrable representative. -/
theorem l2HermitianFirstBornOperatorCurve_ofFunction (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (z : ℂ) (t : Icc (0:ℝ) 1) :
    l2HermitianFirstBornOperatorCurve (intervalL2OfFunction φ hφ) z t =
      hermitianColumns (0,-I*oscillatoryIntegral (I*z) t (fun s => (φ s).2))
        (I*oscillatoryIntegral (-I*z) t (fun s => (φ s).1),0) := by
  have h₁ := l2OscillatoryCurve_apply_ofFunction (-I*z) _ hφ.fst t
  have h₂ := l2OscillatoryCurve_apply_ofFunction (I*z) _ hφ.snd t
  change hermitianColumns (0,-I*l2OscillatoryCurve (I*z) (hφ.snd.toLp _) t)
    (I*l2OscillatoryCurve (-I*z) (hφ.fst.toLp _) t,0) = _
  rw [h₁,h₂]

/-- The weighted Hermitian norm is the exact oscillatory expression of the original function. -/
theorem l2NormalizedHermitianFirstBorn_ofFunction (φ : ℝ → ℂ × ℂ)
    (hφ : MemLp φ 2 (volume.restrict (Ioc 0 1))) (z : ℂ) (t : Icc (0:ℝ) 1) :
    l2NormalizedHermitianFirstBorn (intervalL2OfFunction φ hφ) z t =
      Real.exp (-(|z.im| * t.val))*
        max ‖oscillatoryIntegral (-I*z) t (fun s => (φ s).1)‖
          ‖oscillatoryIntegral (I*z) t (fun s => (φ s).2)‖ := by
  change Real.exp _ * ‖l2HermitianFirstBornOperatorCurve (intervalL2OfFunction φ hφ) z t‖ = _
  rw [l2HermitianFirstBornOperatorCurve_ofFunction,norm_hermitianColumns_offDiagonal]
  simp only [norm_mul,norm_neg,norm_I,one_mul]

end NLS.ZakharovShabat
