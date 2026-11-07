import NLS.MKdV.QuasiHillL2DirichletEigenstate
import NLS.Fourier.UnitIntervalDirichletIdentification
import NLS.Fourier.IntervalL2BoundedMultiplier

/-! # Full interval H1 regularity of both physical weak-state components

The original L2 Miura profile is only square integrable. Continuity of the
actual state on the compact interval makes each coefficient product L2,
so both classical derivatives are square integrable. The quasi-derivative
is not required to have matching endpoint values.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.FunctionalAnalysis
open NLS.Fourier
namespace NLS.MKdV

/-- The physical weak state gives its actual scalar position row. -/
theorem IsQuasiHillL2Solution.position_row (u : NLS.Coeff 2) (lambda : ℂ)
    (w : Curve (ℂ × ℂ)) (hw : IsQuasiHillL2Solution u lambda w) :
    ∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt (fun t => (extend w t).1)
      (unitL2SynthesisEquiv u x*(extend w x).1+(extend w x).2) x := by
  filter_upwards [hw.2] with x hx
  have h := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x hx
  simpa only [quasiHillCoefficient_apply] using! h

/-- The physical weak state gives its actual quasi-derivative row. -/
theorem IsQuasiHillL2Solution.quasiDerivative_row (u : NLS.Coeff 2) (lambda : ℂ)
    (w : Curve (ℂ × ℂ)) (hw : IsQuasiHillL2Solution u lambda w) :
    ∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt (fun t => (extend w t).2)
      (-lambda*(extend w x).1-unitL2SynthesisEquiv u x*(extend w x).2) x := by
  filter_upwards [hw.2] with x hx
  have h := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x hx
  simpa only [quasiHillCoefficient_apply] using! h

/-- BOTH actual weak-state components lie in the original classical interval H1
space, including their endpoint values. Only the original L2 profile is assumed. -/
theorem IsQuasiHillL2Solution.intervalH1 (u : NLS.Coeff 2) (lambda : ℂ)
    (w : Curve (ℂ × ℂ)) (hw : IsQuasiHillL2Solution u lambda w) :
    HasIntervalH1Regularity (fun x => (extend w x).1) ∧
      HasIntervalH1Regularity (fun x => (extend w x).2) := by
  let Y := fun x => (extend w x).1
  let G := fun x => (extend w x).2
  have hYc : Continuous Y := (continuous_extend w).fst
  have hGc : Continuous G := (continuous_extend w).snd
  have hYm := memLp_two_interval hYc 0 1 (by norm_num)
  have hGm := memLp_two_interval hGc 0 1 (by norm_num)
  obtain ⟨KY,hKY⟩ := isCompact_Icc.exists_bound_of_continuousOn hYc.continuousOn
  obtain ⟨KG,hKG⟩ := isCompact_Icc.exists_bound_of_continuousOn hGc.continuousOn
  have hUY : MemLp (fun x => unitL2SynthesisEquiv u x*Y x) 2 (volume.restrict (Ioc 0 1)) := by
    simpa only [mul_comm] using memLp_unitInterval_bounded_mul (unitL2SynthesisEquiv u) Y
      (Lp.memLp _) hYc KY hKY
  have hUG : MemLp (fun x => unitL2SynthesisEquiv u x*G x) 2 (volume.restrict (Ioc 0 1)) := by
    simpa only [mul_comm] using memLp_unitInterval_bounded_mul (unitL2SynthesisEquiv u) G
      (Lp.memLp _) hGc KG hKG
  have hYd : MemLp (deriv Y) 2 (volume.restrict (Ioc 0 1)) := by
    apply (memLp_congr_ae ?_).mp (hUY.add hGm)
    filter_upwards [hw.position_row u lambda w] with x hx
    exact hx.deriv.symm
  have hGd : MemLp (deriv G) 2 (volume.restrict (Ioc 0 1)) := by
    have hforce : MemLp (fun x => -lambda*Y x-unitL2SynthesisEquiv u x*G x)
        2 (volume.restrict (Ioc 0 1)) := (hYm.const_mul (-lambda)).sub hUG
    apply (memLp_congr_ae ?_).mp hforce
    filter_upwards [hw.quasiDerivative_row u lambda w] with x hx
    exact hx.deriv.symm
  exact ⟨⟨absolutelyContinuousOnInterval_clm hw.1 (ContinuousLinearMap.fst ℝ ℂ ℂ),hYd⟩,
    ⟨absolutelyContinuousOnInterval_clm hw.1 (ContinuousLinearMap.snd ℝ ℂ ℂ),hGd⟩⟩

end NLS.MKdV
