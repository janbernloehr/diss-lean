import NLS.ZakharovShabat.L2WholeLineIntegralEquation
import NLS.ZakharovShabat.ContinuousPotentialL2Class

/-! # Actual whole-line solutions for continuous period-one potentials

The checked physical L2 continuation satisfies its original continuous
ODE at every real time, including period seams. It is not replaced by a
new fundamental solution or by a prescribed monodromy.
-/
noncomputable section
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

def periodicProfileUnitCurve (Φ : C(ℝ,ℂ × ℂ)) : Curve (ℂ × ℂ) :=
  ⟨fun t => Φ t,Φ.continuous.comp continuous_subtype_val⟩

theorem l2WholeLinePotential_periodicProfile_ae (Φ : C(ℝ,ℂ × ℂ))
    (hp : Function.Periodic Φ 1) :
    l2WholeLinePotential (continuousPotentialL2Class (periodicProfileUnitCurve Φ)) =ᵐ[volume] Φ := by
  let u := continuousPotentialL2Class (periodicProfileUnitCurve Φ)
  have hbase : l2WholeLinePotential u =ᵐ[volume.restrict (Ioc (0:ℝ) 1)] Φ := by
    filter_upwards [l2WholeLinePotential_ae_unit u,continuousPotentialL2Class_representative (periodicProfileUnitCurve Φ),
      ae_restrict_mem measurableSet_Ioc] with t ht hu htmem
    rw [ht,hu,extend_coe _ ⟨t,htmem.1.le,htmem.2⟩]
    rfl
  have hperiod (n : ℤ) : ∀ᵐ t : ℝ,t ∈ Ioc (n:ℝ) ((n:ℝ)+1) → l2WholeLinePotential u t = Φ t := by
    have h : ∀ᵐ t ∂volume.restrict (Ioc (n:ℝ) ((n:ℝ)+1)),
        l2WholeLinePotential u (t-n) = Φ (t-n) :=
      (measurePreserving_period_sub_int n).quasiMeasurePreserving.ae hbase
    rw [ae_restrict_iff' measurableSet_Ioc] at h
    filter_upwards [h] with t ht
    intro hm
    have he := ht hm
    rw [show l2WholeLinePotential u (t-n) = l2WholeLinePotential u t from
      congrFun (l2WholeLinePotential_comp_sub_int u n) t] at he
    have hp' : Φ (t-n) = Φ t := by simpa only [zsmul_eq_mul,mul_one] using hp.sub_zsmul_eq n (x := t)
    exact he.trans hp'
  filter_upwards [ae_all_iff.mpr hperiod] with t ht
  apply ht (⌈t⌉-1)
  simp only [Int.cast_sub,Int.cast_one,sub_add_cancel,mem_Ioc]
  exact ⟨by linarith [Int.ceil_lt_add_one t],Int.le_ceil t⟩

def periodicClassicalSolution (Φ : C(ℝ,ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) : ℝ → ℂ × ℂ :=
  l2WholeLineSolution (continuousPotentialL2Class (periodicProfileUnitCurve Φ)) z ![v.1,v.2]

@[simp] theorem periodicClassicalSolution_zero (Φ : C(ℝ,ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    periodicClassicalSolution Φ z v 0 = v := by
  simp [periodicClassicalSolution]

theorem continuous_periodicClassicalSolution (Φ : C(ℝ,ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ) :
    Continuous (periodicClassicalSolution Φ z v) := continuous_l2WholeLineSolution _ _ _

theorem periodicClassicalSolution_eq_integral (Φ : C(ℝ,ℂ × ℂ))
    (hp : Function.Periodic Φ 1) (z : ℂ) (v : ℂ × ℂ) (t : ℝ) :
    periodicClassicalSolution Φ z v t = v+
      ∫ s in (0:ℝ)..t,classicalODECoefficient (Φ s) z (periodicClassicalSolution Φ z v s) := by
  have h := l2WholeLineSolution_eq_integral (continuousPotentialL2Class (periodicProfileUnitCurve Φ)) z ![v.1,v.2] t
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at h
  apply h.trans
  congr 1
  apply intervalIntegral.integral_congr_ae
  filter_upwards [l2WholeLinePotential_periodicProfile_ae Φ hp] with s hs _
  rw [hs]
  rfl

theorem hasDerivAt_periodicClassicalSolution (Φ : C(ℝ,ℂ × ℂ))
    (hp : Function.Periodic Φ 1) (z : ℂ) (v : ℂ × ℂ) (t : ℝ) :
    HasDerivAt (periodicClassicalSolution Φ z v)
      (classicalODECoefficient (Φ t) z (periodicClassicalSolution Φ z v t)) t := by
  let f := fun s => classicalODECoefficient (Φ s) z (periodicClassicalSolution Φ z v s)
  have hc : Continuous f := by
    apply Continuous.prodMk
    · exact (continuous_const.mul (continuous_periodicClassicalSolution Φ z v).fst).add
        ((continuous_const.mul Φ.continuous.fst).mul (continuous_periodicClassicalSolution Φ z v).snd)
    · exact ((continuous_const.mul Φ.continuous.snd).mul (continuous_periodicClassicalSolution Φ z v).fst).add
        (continuous_const.mul (continuous_periodicClassicalSolution Φ z v).snd)
  have he : periodicClassicalSolution Φ z v = fun r => v+∫ s in (0:ℝ)..r,f s :=
    funext (periodicClassicalSolution_eq_integral Φ hp z v)
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (0:ℝ) t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).const_add v
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun r => congrFun he r))

theorem periodicClassicalSolution_eq_classical (Φ : C(ℝ,ℂ × ℂ))
    (hp : Function.Periodic Φ 1) (z : ℂ) (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    periodicClassicalSolution Φ z v t = classicalSolution (periodicProfileUnitCurve Φ) z v t :=
  classicalSolution_unique (periodicProfileUnitCurve Φ) z v _
    (continuous_periodicClassicalSolution Φ z v).continuousOn (periodicClassicalSolution_zero Φ z v)
    (fun s _ => hasDerivAt_periodicClassicalSolution Φ hp z v s) t.property

end NLS.ZakharovShabat
