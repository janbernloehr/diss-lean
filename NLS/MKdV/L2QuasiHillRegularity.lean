import NLS.MKdV.L2QuasiHillSolution
import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity

/-! # Scalar H1 regularity of the actual rough quasi-Hill state

Both position and quasi-derivative are absolutely continuous and have
square-integrable first derivatives. No pointwise regularity of the L2
profile is required. The derivative identities hold almost everywhere.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.FunctionalAnalysis
namespace NLS.MKdV

def l2QuasiHillPosition (u : IntervalL2) (μ : ℂ) (v : ℂ × ℂ) : Curve ℂ :=
  ⟨fun t => (l2QuasiHillSolution u μ v t).1,(l2QuasiHillSolution u μ v).continuous.fst⟩

def l2QuasiHillMomentum (u : IntervalL2) (μ : ℂ) (v : ℂ × ℂ) : Curve ℂ :=
  ⟨fun t => (l2QuasiHillSolution u μ v t).2,(l2QuasiHillSolution u μ v).continuous.snd⟩

theorem absolutelyContinuous_l2QuasiHillPosition (u : IntervalL2) (μ : ℂ) (v : ℂ × ℂ) :
    AbsolutelyContinuousOnInterval (extend (l2QuasiHillPosition u μ v)) 0 1 :=
  absolutelyContinuousOnInterval_clm (absolutelyContinuousOnInterval_l2QuasiHillSolution u μ v)
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).restrictScalars ℝ)

theorem absolutelyContinuous_l2QuasiHillMomentum (u : IntervalL2) (μ : ℂ) (v : ℂ × ℂ) :
    AbsolutelyContinuousOnInterval (extend (l2QuasiHillMomentum u μ v)) 0 1 :=
  absolutelyContinuousOnInterval_clm (absolutelyContinuousOnInterval_l2QuasiHillSolution u μ v)
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).restrictScalars ℝ)

theorem ae_deriv_l2QuasiHillPosition (u : IntervalL2) (μ : ℂ) (v : ℂ × ℂ) :
    deriv (extend (l2QuasiHillPosition u μ v)) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun s => u s*extend (l2QuasiHillPosition u μ v) s+extend (l2QuasiHillMomentum u μ v) s) := by
  filter_upwards [ae_hasDerivAt_l2QuasiHillSolution u μ v] with s hs
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,
    one_smul,ContinuousLinearMap.coe_fst',quasiHillCoefficient_apply] using!
      (HasFDerivAt.hasDerivAt hs.fst).deriv

theorem ae_deriv_l2QuasiHillMomentum (u : IntervalL2) (μ : ℂ) (v : ℂ × ℂ) :
    deriv (extend (l2QuasiHillMomentum u μ v)) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun s => -μ*extend (l2QuasiHillPosition u μ v) s-u s*extend (l2QuasiHillMomentum u μ v) s) := by
  filter_upwards [ae_hasDerivAt_l2QuasiHillSolution u μ v] with s hs
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.toSpanSingleton_apply,
    one_smul,ContinuousLinearMap.coe_snd',quasiHillCoefficient_apply] using!
      (HasFDerivAt.hasDerivAt hs.snd).deriv

/-- Multiplication by an actual continuous interval curve preserves L2. -/
theorem memLp_intervalL2_mul_curve (u : IntervalL2) (f : Curve ℂ) :
    MemLp (fun s => u s*extend f s) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  (curveBoundedExtension ℂ f).memLp_top.mul (Lp.memLp u)

/-- Every continuous interval curve has its usual square-integrable representative. -/
theorem memLp_extend_scalarCurve (f : Curve ℂ) :
    MemLp (extend f) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  exact (memLp_extend_continuousPotential (f.prodMk f)).fst

theorem memLp_deriv_l2QuasiHillPosition (u : IntervalL2) (μ : ℂ) (v : ℂ × ℂ) :
    MemLp (deriv (extend (l2QuasiHillPosition u μ v))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  (memLp_congr_ae (ae_deriv_l2QuasiHillPosition u μ v)).mpr
    (memLp_intervalL2_mul_curve u (l2QuasiHillPosition u μ v) |>.add
      (memLp_extend_scalarCurve (l2QuasiHillMomentum u μ v)))

theorem memLp_deriv_l2QuasiHillMomentum (u : IntervalL2) (μ : ℂ) (v : ℂ × ℂ) :
    MemLp (deriv (extend (l2QuasiHillMomentum u μ v))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  (memLp_congr_ae (ae_deriv_l2QuasiHillMomentum u μ v)).mpr
    ((memLp_extend_scalarCurve (l2QuasiHillPosition u μ v)).const_mul (-μ) |>.sub
      (memLp_intervalL2_mul_curve u (l2QuasiHillMomentum u μ v)))

end NLS.MKdV
