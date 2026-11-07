import NLS.MKdV.QuasiHillL2Volterra
import NLS.MKdV.QuasiHillL2StateSobolev

/-! # Actual rough forced scalar IVPs

The forcing is the negative preceding position. The full integral equation
gives absolute continuity and the weak ODE; both state components are H1.
Uniqueness uses the verified rough homogeneous IVP on the same physical interval.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.MKdV
open NLS.Fourier

/-- The actual forced physical scalar state, with its preceding continuous state. -/
def IsQuasiHillL2ForcedSolution (u : Coeff 2) (lambda : ℂ)
    (v w : Curve (ℂ × ℂ)) : Prop :=
  AbsolutelyContinuousOnInterval (extend w) 0 1 ∧
    ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1), HasDerivAt (extend w)
      (quasiHillCoefficient (unitL2SynthesisEquiv u x) lambda (extend w x)+(0,-(extend v x).1)) x

/-- The literal full Volterra equation supplies a genuine AC forced physical solution. -/
theorem isQuasiHillL2ForcedSolution_of_volterra (u : Coeff 2) (lambda : ℂ)
    (v w : Curve (ℂ × ℂ)) (c : ℂ × ℂ)
    (he : w = ContinuousMap.const _ c+quasiHillL2Volterra u lambda w+quasiHillL2EnergyVolterra v) :
    IsQuasiHillL2ForcedSolution u lambda v w := by
  have hA := intervalIntegrable_quasiHillL2Coefficient u lambda w ⟨1,by constructor <;> norm_num⟩
  have hc : Continuous (fun x : ℝ => ((0:ℂ),-(extend v x).1)) :=
    continuous_const.prodMk (continuous_extend v).fst.neg
  have hB := hc.intervalIntegrable (μ := volume) 0 1
  apply curve_integral_regularity w c _ (hA.add hB)
  intro t
  have ht := congrArg (fun r : Curve (ℂ × ℂ) => r t) he
  change w t = (c+quasiHillL2Volterra u lambda w t)+quasiHillL2EnergyVolterra v t at ht
  rw [quasiHillL2Volterra_apply_integral, quasiHillL2EnergyVolterra_apply_integral] at ht
  have hAt := intervalIntegrable_quasiHillL2Coefficient u lambda w t
  have hBt := hc.intervalIntegrable (μ := volume) 0 t.val
  rw [intervalIntegral.integral_add hAt hBt]
  simpa only [add_assoc] using ht

theorem IsQuasiHillL2ForcedSolution.position_row (u : Coeff 2) (lambda : ℂ)
    (v w : Curve (ℂ × ℂ)) (hw : IsQuasiHillL2ForcedSolution u lambda v w) :
    ∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt (fun t => (extend w t).1)
      (unitL2SynthesisEquiv u x*(extend w x).1+(extend w x).2) x := by
  filter_upwards [hw.2] with x hx
  have h := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x hx
  change HasDerivAt (fun t => (extend w t).1)
    ((unitL2SynthesisEquiv u x*(extend w x).1+(extend w x).2)+0) x at h
  simpa only [add_zero] using h

theorem IsQuasiHillL2ForcedSolution.quasiDerivative_row (u : Coeff 2) (lambda : ℂ)
    (v w : Curve (ℂ × ℂ)) (hw : IsQuasiHillL2ForcedSolution u lambda v w) :
    ∀ᵐ x ∂volume.restrict (Ioc 0 1), HasDerivAt (fun t => (extend w t).2)
      (-lambda*(extend w x).1-unitL2SynthesisEquiv u x*(extend w x).2-(extend v x).1) x := by
  filter_upwards [hw.2] with x hx
  have h := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt x hx
  simpa only [quasiHillCoefficient_apply, Prod.snd_add, sub_eq_add_neg] using! h

/-- Both actual forced state components have full interval H1 regularity. -/
theorem IsQuasiHillL2ForcedSolution.intervalH1 (u : Coeff 2) (lambda : ℂ)
    (v w : Curve (ℂ × ℂ)) (hw : IsQuasiHillL2ForcedSolution u lambda v w) :
    HasIntervalH1Regularity (fun x => (extend w x).1) ∧
      HasIntervalH1Regularity (fun x => (extend w x).2) := by
  let Y := fun x : ℝ => (extend w x).1
  let G := fun x : ℝ => (extend w x).2
  have hYc : Continuous Y := (continuous_extend w).fst
  have hGc : Continuous G := (continuous_extend w).snd
  have hYm := memLp_two_interval hYc 0 1 (by norm_num)
  have hGm := memLp_two_interval hGc 0 1 (by norm_num)
  have hVm := memLp_two_interval (continuous_extend v).fst 0 1 (by norm_num)
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
    filter_upwards [hw.position_row u lambda v w] with x hx
    exact hx.deriv.symm
  have hGd : MemLp (deriv G) 2 (volume.restrict (Ioc 0 1)) := by
    have hforce : MemLp (fun x => -lambda*Y x-unitL2SynthesisEquiv u x*G x-(extend v x).1)
        2 (volume.restrict (Ioc 0 1)) := ((hYm.const_mul (-lambda)).sub hUG).sub hVm
    apply (memLp_congr_ae ?_).mp hforce
    filter_upwards [hw.quasiDerivative_row u lambda v w] with x hx
    exact hx.deriv.symm
  exact ⟨⟨absolutelyContinuousOnInterval_clm hw.1 (ContinuousLinearMap.fst ℝ ℂ ℂ),hYd⟩,
    ⟨absolutelyContinuousOnInterval_clm hw.1 (ContinuousLinearMap.snd ℝ ℂ ℂ),hGd⟩⟩

/-- The preceding state and actual initial position/quasi-derivative uniquely
determine the forced physical solution. -/
theorem IsQuasiHillL2ForcedSolution.eq_of_initial_eq (u : Coeff 2) (lambda : ℂ)
    (v w z : Curve (ℂ × ℂ)) (hw : IsQuasiHillL2ForcedSolution u lambda v w)
    (hz : IsQuasiHillL2ForcedSolution u lambda v z)
    (hi : w ⟨0,by constructor <;> norm_num⟩ = z ⟨0,by constructor <;> norm_num⟩) : w = z := by
  have ha : AbsolutelyContinuousOnInterval (extend (w-z)) 0 1 := hw.1.sub hz.1
  have hd : ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1), HasDerivAt (extend (w-z))
      (quasiHillCoefficient (unitL2SynthesisEquiv u x) lambda (extend (w-z) x)) x := by
    filter_upwards [hw.2, hz.2] with x hx hy
    have h := hx.sub hy
    rw [add_sub_add_right_eq_sub, ← map_sub] at h
    exact h
  have he := quasiHillL2SolutionCurve_unique_of_ac u lambda (w-z) ha hd
  have h0 : (w-z) ⟨0,by constructor <;> norm_num⟩ = 0 := by
    change w _-z _ = 0
    rw [hi, sub_self]
  rw [h0, quasiHillL2SolutionCurve_zero_initial] at he
  exact sub_eq_zero.mp he

end NLS.MKdV
