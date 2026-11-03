import NLS.MKdV.QuasiHillL2InitialValue
import NLS.FunctionalAnalysis.CurveIntegralEquation

/-! # The actual scalar rough Volterra equation, affine in energy

All operations act in the full uniform curve norm. The original L2 scalar
multiplier is integrated against the actual continuous state, with the
physical scalar initial position and quasi-derivative unchanged.
-/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.MKdV
open NLS.Fourier NLS.ZakharovShabat

private def firstCurve : Curve (ℂ × ℂ) →L[ℂ] Curve ℂ :=
  ContinuousLinearMap.compLeftContinuous ℂ _ (ContinuousLinearMap.fst ℂ ℂ ℂ)
private def secondCurve : Curve (ℂ × ℂ) →L[ℂ] Curve ℂ :=
  ContinuousLinearMap.compLeftContinuous ℂ _ (ContinuousLinearMap.snd ℂ ℂ ℂ)
private def leftCurve : Curve ℂ →L[ℂ] Curve (ℂ × ℂ) :=
  ContinuousLinearMap.compLeftContinuous ℂ _ ((ContinuousLinearMap.id ℂ ℂ).prod 0)
private def rightCurve : Curve ℂ →L[ℂ] Curve (ℂ × ℂ) :=
  ContinuousLinearMap.compLeftContinuous ℂ _ ((0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ))

@[simp] private theorem firstCurve_apply (w : Curve (ℂ × ℂ)) (t : Icc (0:ℝ) 1) :
    firstCurve w t = (w t).1 := rfl
@[simp] private theorem secondCurve_apply (w : Curve (ℂ × ℂ)) (t : Icc (0:ℝ) 1) :
    secondCurve w t = (w t).2 := rfl
@[simp] private theorem leftCurve_apply (w : Curve ℂ) (t : Icc (0:ℝ) 1) :
    leftCurve w t = (w t,0) := rfl
@[simp] private theorem rightCurve_apply (w : Curve ℂ) (t : Icc (0:ℝ) 1) :
    rightCurve w t = (0,w t) := rfl
@[simp] private theorem extend_firstCurve (w : Curve (ℂ × ℂ)) (x : ℝ) :
    extend (firstCurve w) x = (extend w x).1 := rfl
@[simp] private theorem extend_secondCurve (w : Curve (ℂ × ℂ)) (x : ℝ) :
    extend (secondCurve w) x = (extend w x).2 := rfl

/-- The scalar L2 part of the actual quasi-Hill integral operator. -/
def quasiHillL2ProfileVolterra (u : Coeff 2) : Curve (ℂ × ℂ) →L[ℂ] Curve (ℂ × ℂ) :=
  leftCurve.comp ((l2ScalarVolterra (unitL2SynthesisEquiv u)).comp firstCurve)-
    rightCurve.comp ((l2ScalarVolterra (unitL2SynthesisEquiv u)).comp secondCurve)

/-- The fixed position/quasi-derivative coupling. -/
def quasiHillL2FreeVolterra : Curve (ℂ × ℂ) →L[ℂ] Curve (ℂ × ℂ) :=
  leftCurve.comp ((primitive (E := ℂ)).comp secondCurve)

/-- The exact scalar energy slope, with forcing in the second row only. -/
def quasiHillL2EnergyVolterra : Curve (ℂ × ℂ) →L[ℂ] Curve (ℂ × ℂ) :=
  -rightCurve.comp ((primitive (E := ℂ)).comp firstCurve)

/-- The full original rough scalar Volterra operator. -/
def quasiHillL2Volterra (u : Coeff 2) (lambda : ℂ) : Curve (ℂ × ℂ) →L[ℂ] Curve (ℂ × ℂ) :=
  quasiHillL2ProfileVolterra u+quasiHillL2FreeVolterra+lambda • quasiHillL2EnergyVolterra

/-- Energy dependence is literally affine in the actual uniform operator norm. -/
theorem quasiHillL2Volterra_add_energy (u : Coeff 2) (lambda t : ℂ) :
    quasiHillL2Volterra u (lambda+t) = quasiHillL2Volterra u lambda+t • quasiHillL2EnergyVolterra := by
  unfold quasiHillL2Volterra
  module

/-- The actual energy slope has zero position component. -/
theorem quasiHillL2EnergyVolterra_components (w : Curve (ℂ × ℂ)) (t : Icc (0:ℝ) 1) :
    quasiHillL2EnergyVolterra w t = (0,-∫ x in (0:ℝ)..t.val, (extend w x).1) := by
  simp [quasiHillL2EnergyVolterra, primitive_apply]

/-- Its exact physical forcing is the negative preceding scalar position. -/
theorem quasiHillL2EnergyVolterra_apply_integral (w : Curve (ℂ × ℂ)) (t : Icc (0:ℝ) 1) :
    quasiHillL2EnergyVolterra w t = ∫ x in (0:ℝ)..t.val, (0,-(extend w x).1) := by
  have hY := (continuous_extend w).fst.intervalIntegrable (μ := volume) 0 t.val
  have h0 := (continuous_const : Continuous (fun _ : ℝ => (0:ℂ))).intervalIntegrable
    (μ := volume) 0 t.val
  rw [quasiHillL2EnergyVolterra_components]
  simp_rw [intervalIntegral.integral_of_le t.property.1]
  have hneg : IntervalIntegrable (fun x : ℝ => -(extend w x).1) volume 0 t.val := hY.neg
  rw [integral_pair h0.1 hneg.1]
  simp only [integral_zero, integral_neg]

/-- Coordinate integrals retain the exact physical unit-interval normalization. -/
theorem quasiHillL2Volterra_components (u : Coeff 2) (lambda : ℂ)
    (w : Curve (ℂ × ℂ)) (t : Icc (0:ℝ) 1) :
    quasiHillL2Volterra u lambda w t =
      ((∫ x in (0:ℝ)..t.val, unitL2SynthesisEquiv u x*(extend w x).1)+
        (∫ x in (0:ℝ)..t.val, (extend w x).2),
       -(∫ x in (0:ℝ)..t.val, unitL2SynthesisEquiv u x*(extend w x).2)-
        lambda*(∫ x in (0:ℝ)..t.val, (extend w x).1)) := by
  simp [quasiHillL2Volterra, quasiHillL2ProfileVolterra, quasiHillL2FreeVolterra,
    quasiHillL2EnergyVolterra, primitive_apply]
  ring

/-- Every continuous state has an integrable actual rough quasi-Hill right-hand side. -/
theorem intervalIntegrable_quasiHillL2Coefficient (u : Coeff 2) (lambda : ℂ)
    (w : Curve (ℂ × ℂ)) (t : Icc (0:ℝ) 1) :
    IntervalIntegrable (fun x => quasiHillCoefficient (unitL2SynthesisEquiv u x) lambda (extend w x))
      volume 0 t.val := by
  have hUY := intervalIntegrable_intervalL2_mul (unitL2SynthesisEquiv u)
    (curveBoundedExtension ℂ (firstCurve w)) t
  have hUG := intervalIntegrable_intervalL2_mul (unitL2SynthesisEquiv u)
    (curveBoundedExtension ℂ (secondCurve w)) t
  have hY := (continuous_extend w).fst.intervalIntegrable (μ := volume) 0 t.val
  have hG := (continuous_extend w).snd.intervalIntegrable (μ := volume) 0 t.val
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le t.property.1).mpr
  simpa only [IntegrableOn, quasiHillCoefficient_apply, curveBoundedExtension_apply,
    extend_firstCurve, extend_secondCurve] using!
      ((hUY.add hG).1.prodMk ((hY.const_mul (-lambda)).sub hUG).1)

/-- The bounded operator is exactly the original physical coefficient integral. -/
theorem quasiHillL2Volterra_apply_integral (u : Coeff 2) (lambda : ℂ)
    (w : Curve (ℂ × ℂ)) (t : Icc (0:ℝ) 1) :
    quasiHillL2Volterra u lambda w t =
      ∫ x in (0:ℝ)..t.val, quasiHillCoefficient (unitL2SynthesisEquiv u x) lambda (extend w x) := by
  have hUY := intervalIntegrable_intervalL2_mul (unitL2SynthesisEquiv u)
    (curveBoundedExtension ℂ (firstCurve w)) t
  have hUG := intervalIntegrable_intervalL2_mul (unitL2SynthesisEquiv u)
    (curveBoundedExtension ℂ (secondCurve w)) t
  simp only [curveBoundedExtension_apply, extend_firstCurve, extend_secondCurve] at hUY hUG
  have hY := (continuous_extend w).fst.intervalIntegrable (μ := volume) 0 t.val
  have hG := (continuous_extend w).snd.intervalIntegrable (μ := volume) 0 t.val
  rw [quasiHillL2Volterra_components]
  simp only [quasiHillCoefficient_apply]
  simp_rw [intervalIntegral.integral_of_le t.property.1]
  rw [integral_pair (hUY.add hG).1 ((hY.const_mul (-lambda)).sub hUG).1,
    integral_add hUY.1 hG.1, integral_sub (hY.const_mul (-lambda)).1 hUG.1,
    integral_const_mul]
  apply Prod.ext
  · rfl
  · dsimp
    ring

/-- The independent normalized rough IVP satisfies the full scalar Volterra equation. -/
theorem quasiHillL2SolutionCurve_eq_volterra (u : Coeff 2) (lambda : ℂ) (v : ℂ × ℂ) :
    quasiHillL2SolutionCurve u lambda v = ContinuousMap.const _ v+
      quasiHillL2Volterra u lambda (quasiHillL2SolutionCurve u lambda v) := by
  apply ContinuousMap.ext
  intro t
  rw [ContinuousMap.add_apply, ContinuousMap.const_apply, quasiHillL2Volterra_apply_integral]
  have h := curve_eq_initial_add_integral_of_ac (quasiHillL2SolutionCurve u lambda v)
    (fun x => quasiHillCoefficient (unitL2SynthesisEquiv u x) lambda
      (extend (quasiHillL2SolutionCurve u lambda v) x))
    (absolutelyContinuousOnInterval_quasiHillL2SolutionCurve u lambda v)
    (intervalIntegrable_quasiHillL2Coefficient u lambda _ ⟨1,by constructor <;> norm_num⟩)
    (ae_hasDerivAt_quasiHillL2SolutionCurve u lambda v) t
  rwa [quasiHillL2SolutionCurve_zero] at h

end NLS.MKdV
