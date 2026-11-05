import NLS.Fourier.IntervalCurveL2
import NLS.FunctionalAnalysis.IntervalH1Product

/-! # Polynomial multiplication on the continuous/L2 H1 graph

The formulas are bounded polynomial maps on graph pairs. On actual H1
curves the derivative coordinate is exactly the physical derivative of
the product, allowing parameter derivatives without representative choices.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.FunctionalAnalysis
namespace NLS.Fourier

def intervalH1ProductDerivative (a b : Curve ℂ × IntervalL2) : IntervalL2 :=
  intervalCurveMultiplication b.1 a.2+intervalCurveMultiplication a.1 b.2

def intervalH1MassProduct (m : ℕ) (a b : Curve ℂ × IntervalL2) : IntervalL2 :=
  ((((m : ℝ)+1 : ℝ) : ℂ)) • intervalCurveL2 (a.1*b.1)-intervalH1ProductDerivative a b

theorem analyticOnNhd_intervalH1ProductDerivative_joint :
    AnalyticOnNhd ℂ (fun p : (Curve ℂ × IntervalL2) × (Curve ℂ × IntervalL2) =>
      intervalH1ProductDerivative p.1 p.2) univ := by
  intro p _
  have hy : AnalyticAt ℂ (fun p : (Curve ℂ × IntervalL2) × (Curve ℂ × IntervalL2) => p.1.1) p :=
    analyticAt_fst.comp (f := Prod.fst) analyticAt_fst
  have hdy : AnalyticAt ℂ (fun p : (Curve ℂ × IntervalL2) × (Curve ℂ × IntervalL2) => p.1.2) p :=
    analyticAt_snd.comp (f := Prod.fst) analyticAt_fst
  have hz : AnalyticAt ℂ (fun p : (Curve ℂ × IntervalL2) × (Curve ℂ × IntervalL2) => p.2.1) p :=
    analyticAt_fst.comp (f := Prod.snd) analyticAt_snd
  have hdz : AnalyticAt ℂ (fun p : (Curve ℂ × IntervalL2) × (Curve ℂ × IntervalL2) => p.2.2) p :=
    analyticAt_snd.comp (f := Prod.snd) analyticAt_snd
  exact ((intervalCurveMultiplication.analyticAt_bilinear _).comp₂ hz hdy).add
    ((intervalCurveMultiplication.analyticAt_bilinear _).comp₂ hy hdz)

theorem analyticOnNhd_intervalH1MassProduct_joint (m : ℕ) :
    AnalyticOnNhd ℂ (fun p : (Curve ℂ × IntervalL2) × (Curve ℂ × IntervalL2) =>
      intervalH1MassProduct m p.1 p.2) univ := by
  intro p hp
  have hy : AnalyticAt ℂ (fun p : (Curve ℂ × IntervalL2) × (Curve ℂ × IntervalL2) => p.1.1) p :=
    analyticAt_fst.comp (f := Prod.fst) analyticAt_fst
  have hz : AnalyticAt ℂ (fun p : (Curve ℂ × IntervalL2) × (Curve ℂ × IntervalL2) => p.2.1) p :=
    analyticAt_fst.comp (f := Prod.snd) analyticAt_snd
  exact (((intervalCurveL2.analyticAt _).comp (hy.mul hz)).const_smul
    (c := ((((m : ℝ)+1 : ℝ) : ℂ)))).sub (analyticOnNhd_intervalH1ProductDerivative_joint p hp)

theorem intervalH1ProductDerivative_representative (y z : Curve ℂ) (dy dz : IntervalL2)
    (hy : AbsolutelyContinuousOnInterval (extend y) 0 1)
    (hz : AbsolutelyContinuousOnInterval (extend z) 0 1)
    (hdy : dy =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] deriv (extend y))
    (hdz : dz =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] deriv (extend z)) :
    intervalH1ProductDerivative (y,dy) (z,dz) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      deriv (extend (y*z)) := by
  filter_upwards [Lp.coeFn_add (intervalCurveMultiplication z dy) (intervalCurveMultiplication y dz),
    intervalCurveMul_representative z dy,intervalCurveMul_representative y dz,
    hdy,hdz,ae_deriv_curve_mul y z hy hz] with s ha h₁ h₂ hd₁ hd₂ hp
  change (intervalCurveMultiplication z dy+intervalCurveMultiplication y dz) s = _
  rw [ha]
  simp only [Pi.add_apply,intervalCurveMultiplication_apply] at *
  rw [h₁,h₂,hd₁,hd₂,hp]
  ring

theorem intervalH1MassProduct_eq (m : ℕ) (y z : Curve ℂ) (dy dz : IntervalL2)
    (hy : AbsolutelyContinuousOnInterval (extend y) 0 1)
    (hz : AbsolutelyContinuousOnInterval (extend z) 0 1)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hz₂ : MemLp (deriv (extend z)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hdy : dy =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] deriv (extend y))
    (hdz : dz =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] deriv (extend z)) :
    intervalH1MassProduct m (y,dy) (z,dz) =
      ((((m : ℝ)+1 : ℝ) : ℂ)) • intervalCurveL2 (y*z)-
        (memLp_deriv_curve_mul y z hy hz hy₂ hz₂).toLp (deriv (extend (y*z))) := by
  have he : intervalH1ProductDerivative (y,dy) (z,dz) =
      (memLp_deriv_curve_mul y z hy hz hy₂ hz₂).toLp (deriv (extend (y*z))) := by
    apply Lp.ext
    exact (intervalH1ProductDerivative_representative y z dy dz hy hz hdy hdz).trans
      (memLp_deriv_curve_mul y z hy hz hy₂ hz₂).coeFn_toLp.symm
  exact congrArg (fun d => ((((m : ℝ)+1 : ℝ) : ℂ)) • intervalCurveL2 (y*z)-d) he

end NLS.Fourier
