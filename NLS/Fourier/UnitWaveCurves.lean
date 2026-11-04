import NLS.Fourier.UnitCurveCoefficients
import NLS.Fourier.AbsoluteContinuousCoefficients

/-! # Periodic unit Fourier test curves and their actual derivatives -/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.Fourier

def unitWaveCurve (k : ℤ) : Curve ℂ :=
  ⟨fun t => wave (2*k) t, (continuous_wave _).comp continuous_subtype_val⟩

theorem extend_unitWaveCurve_of_mem (k : ℤ) {x : ℝ} (hx : x∈Icc (0:ℝ) 1) :
    extend (unitWaveCurve k) x=wave (2*k) x := by
  simp only [NLS.LinearVolterra.extend,unitWaveCurve,ContinuousMap.coe_mk,projIcc_of_mem _ hx]

@[simp] theorem unitWaveCurve_endpoints (k : ℤ) :
    extend (unitWaveCurve k) 0=extend (unitWaveCurve k) 1 := by
  rw [extend_unitWaveCurve_of_mem k (by norm_num),extend_unitWaveCurve_of_mem k (by norm_num),
    wave_at_zero,wave_even_at_one]

theorem absolutelyContinuousOnInterval_unitWaveCurve (k : ℤ) :
    AbsolutelyContinuousOnInterval (extend (unitWaveCurve k)) 0 1 := by
  apply absolutelyContinuousOnInterval_congr
    ((contDiff_wave (2*k)).contDiffOn.absolutelyContinuousOnInterval (a := (0:ℝ)) (b := 1))
  intro x hx
  exact (extend_unitWaveCurve_of_mem k (by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hx)).symm

/-- The derivative identity is about the actual clipped extension on the
unit interval; its possible endpoint derivatives do not affect the L2 class. -/
theorem ae_deriv_extend_unitWaveCurve (k : ℤ) :
    deriv (extend (unitWaveCurve k))=ᵐ[volume.restrict (Ioc (0:ℝ) 1)]
      extend ((I*(Real.pi:ℂ)*(2*k:ℤ)) • unitWaveCurve k) := by
  have hmem : ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) 1), x∈Ioo (0:ℝ) 1 := by
    rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hmem] with x hx
  have hnear : extend (unitWaveCurve k) =ᶠ[𝓝 x] wave (2*k) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact extend_unitWaveCurve_of_mem k (Ioo_subset_Icc_self hy)
  have hd : HasDerivAt (extend (unitWaveCurve k)) (I*(Real.pi:ℂ)*(2*k:ℤ)*wave (2*k) x) x :=
    (hasDerivAt_wave (2*k) x).congr_of_eventuallyEq hnear
  rw [hd.deriv]
  change _=I*(Real.pi:ℂ)*(2*k:ℤ)*extend (unitWaveCurve k) x
  rw [extend_unitWaveCurve_of_mem k (Ioo_subset_Icc_self hx)]

theorem unitWaveCurve_derivative_endpoints (k : ℤ) :
    extend ((I*(Real.pi:ℂ)*(2*k:ℤ)) • unitWaveCurve k) 0=
      extend ((I*(Real.pi:ℂ)*(2*k:ℤ)) • unitWaveCurve k) 1 := by
  change I*(Real.pi:ℂ)*(2*k:ℤ)*extend (unitWaveCurve k) 0=
    I*(Real.pi:ℂ)*(2*k:ℤ)*extend (unitWaveCurve k) 1
  rw [unitWaveCurve_endpoints]

end NLS.Fourier
