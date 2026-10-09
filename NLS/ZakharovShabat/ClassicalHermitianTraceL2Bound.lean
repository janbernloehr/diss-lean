import NLS.ZakharovShabat.IntervalHermitianFirstBornBound
import NLS.ZakharovShabat.L2HermitianUniformRemainderBound
import NLS.ZakharovShabat.ClassicalSobolevPotential

/-! # G.2's constants with explicit trace and derivative data

The size below is exactly the maximum of the physical supremum norm and
both coordinate derivative L2 norms. We do not silently identify this size
with the dissertation's unspecified interval H1 norm. The latter comparison
is still needed for the literal source statement.
-/
noncomputable section
open Set MeasureTheory
open NLS.LinearVolterra NLS.ComplexAnalysis NLS.Fourier
namespace NLS.ZakharovShabat

/-- Explicit trace-controlling size, distinct from a chosen Sobolev norm. -/
def classicalTraceL2Size (φ : Curve (ℂ × ℂ)) : ℝ :=
  max ‖φ‖ (max (Real.sqrt (∫ s in (0 : ℝ)..1, ‖deriv (fun r => (extend φ r).1) s‖^2))
    (Real.sqrt (∫ s in (0 : ℝ)..1, ‖deriv (fun r => (extend φ r).2) s‖^2)))

theorem classicalTraceL2Size_nonneg (φ : Curve (ℂ × ℂ)) : 0 ≤ classicalTraceL2Size φ :=
  (norm_nonneg φ).trans (le_max_left _ _)

/-- The actual first Born operator with the factor (2+sqrt(t))/(2|z|).
Regularity is only absolute continuity with square-integrable derivatives. -/
theorem classicalHermitianFirstBorn_le_traceL2Size
    (φ : Curve (ℂ × ℂ))
    (hf : AbsolutelyContinuousOnInterval (fun s => (extend φ s).1) 0 1)
    (hg : AbsolutelyContinuousOnInterval (fun s => (extend φ s).2) 0 1)
    (hdf : MemLp (deriv (fun s => (extend φ s).1)) 2 (volume.restrict (Ioc 0 1)))
    (hdg : MemLp (deriv (fun s => (extend φ s).2)) 2 (volume.restrict (Ioc 0 1)))
    (z : ℂ) (hz : z ≠ 0) (t : Icc (0 : ℝ) 1) :
    classicalNormalizedHermitianFirstBorn φ z t ≤
      (2+Real.sqrt t.val)/(2*‖z‖)*classicalTraceL2Size φ := by
  have hsub : uIcc 0 t.val ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le t.property.1,uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl t.property.2
  have hm : volume.restrict (Ioc (0 : ℝ) t.val) ≤ volume.restrict (Ioc (0 : ℝ) 1) :=
    Measure.restrict_mono_set _ (Ioc_subset_Ioc_right t.property.2)
  have hnorm (s : ℝ) : ‖extend φ s‖ ≤ classicalTraceL2Size φ :=
    (φ.norm_coe_le_norm _).trans (le_max_left _ _)
  have hD : max (Real.sqrt (∫ s in 0..t.val, ‖deriv (fun r => (extend φ r).1) s‖^2))
      (Real.sqrt (∫ s in 0..t.val, ‖deriv (fun r => (extend φ r).2) s‖^2)) ≤
      classicalTraceL2Size φ :=
    (max_le_max (sqrt_integral_norm_sq_le_unit _ hdf t)
      (sqrt_integral_norm_sq_le_unit _ hdg t)).trans (le_max_right _ _)
  have h := intervalHermitianFirstBornOperator_weighted_le_of_trace_L2_bound
    (extend φ) z hz t t.property.1 (hf.mono hsub) (hg.mono hsub)
    (hdf.mono_measure hm) (hdg.mono_measure hm) (classicalTraceL2Size φ) (hnorm 0) (hnorm t) hD
  simpa only [intervalHermitianFirstBornOperator_of_continuous,classicalNormalizedHermitianFirstBorn] using h

/-- G.1 gives the actual remainder bound with precisely 3/(2|z|) and
1+||phi||_2 exp(||phi||_2), using the explicit size defined above. -/
theorem classicalHermitianRemainder_le_traceL2Size
    (φ : Curve (ℂ × ℂ))
    (hf : AbsolutelyContinuousOnInterval (fun s => (extend φ s).1) 0 1)
    (hg : AbsolutelyContinuousOnInterval (fun s => (extend φ s).2) 0 1)
    (hdf : MemLp (deriv (fun s => (extend φ s).1)) 2 (volume.restrict (Ioc 0 1)))
    (hdg : MemLp (deriv (fun s => (extend φ s).2)) 2 (volume.restrict (Ioc 0 1)))
    (z : ℂ) (hz : z ≠ 0) (t : Icc (0 : ℝ) 1) :
    classicalNormalizedHermitianRemainder φ z t ≤
      3/(2*‖z‖)*(1+classicalPotentialL2Norm φ*Real.exp (classicalPotentialL2Norm φ))*
        classicalTraceL2Size φ := by
  let B := 3/(2*‖z‖)*classicalTraceL2Size φ
  have hB : 0 ≤ B := mul_nonneg (by positivity) (classicalTraceL2Size_nonneg φ)
  have hF (s : Icc (0 : ℝ) 1) :
      l2NormalizedHermitianFirstBorn (continuousPotentialL2Class φ) z s ≤ B := by
    rw [l2NormalizedHermitianFirstBorn_of_continuous]
    apply (classicalHermitianFirstBorn_le_traceL2Size φ hf hg hdf hdg z hz s).trans
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by linarith [Real.sqrt_le_one.mpr s.property.2])
        (by positivity)) (classicalTraceL2Size_nonneg φ)
  have h := l2HermitianRemainder_le_of_firstBorn_uniform_unit
    (continuousPotentialL2Class φ) z B hB hF t
  rw [l2NormalizedHermitianRemainder_of_continuous,norm_continuousPotentialL2Class] at h
  exact h.trans_eq (by dsimp [B]; ring)

/-- Every physical H1 Fourier pair supplies the regularity premises; the
right side still displays the actual trace/derivative size, not a coefficient norm. -/
theorem classicalHermitianRemainder_sobolev_le_traceL2Size
    (a : ScalarDomain 2 × ScalarDomain 2) (z : ℂ) (hz : z ≠ 0) (t : Icc (0 : ℝ) 1) :
    classicalNormalizedHermitianRemainder (classicalSobolevPotential a) z t ≤
      3/(2*‖z‖)*(1+classicalPotentialL2Norm (classicalSobolevPotential a)*
        Real.exp (classicalPotentialL2Norm (classicalSobolevPotential a)))*
        classicalTraceL2Size (classicalSobolevPotential a) := by
  obtain ⟨hf,hg,_,_⟩ := classicalSobolevPotential_regular a
  exact classicalHermitianRemainder_le_traceL2Size _ hf hg
    (memLp_deriv_extend_sobolevUnitCurve a.1)
    (memLp_deriv_extend_sobolevUnitCurve a.2) z hz t

end NLS.ZakharovShabat
