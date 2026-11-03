import NLS.MKdV.WeakMiuraFormAnalytic
import NLS.FunctionalAnalysis.IntervalH1Product

/-! # The weak Miura form equals the physical L2 Hill form on H1 lifts

Integration by parts removes the Riccati lift on the actual unit
interval. The two scalar test curves may be periodic, antiperiodic, or
have reciprocal multipliers: only periodicity of their product is used.
-/
noncomputable section
set_option autoImplicit false
open Set Complex MeasureTheory Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.Fourier NLS.FunctionalAnalysis
namespace NLS.MKdV

def physicalL2HillPotentialPairing (y φ : Curve ℂ) : IntervalL2 →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ ⟨1,by constructor <;> norm_num⟩).comp
    (intervalL2PrimitiveCLM (curveBoundedExtension ℂ (y*φ)))

theorem physicalL2HillPotentialPairing_apply (y φ : Curve ℂ) (b : IntervalL2) :
    physicalL2HillPotentialPairing y φ b = ∫ s in (0 : ℝ)..1, b s*(extend y s*extend φ s) := rfl

def physicalL2HillWeakForm (b : IntervalL2) (y φ : Curve ℂ) : ℂ :=
  (∫ s in (0 : ℝ)..1, deriv (extend y) s*deriv (extend φ) s)+physicalL2HillPotentialPairing y φ b

theorem analyticAt_physicalL2HillWeakForm (b : IntervalL2) (y φ : Curve ℂ) :
    AnalyticAt ℂ (fun b => physicalL2HillWeakForm b y φ) b :=
  analyticAt_const.add ((physicalL2HillPotentialPairing y φ).analyticAt b)

/-- For an actual H1 lift, the form depends only on its physical Miura
image, for every H1 pair whose product has matching endpoint values. -/
theorem shiftedMiuraWeakForm_eq_physicalL2_of_H1 (u b : IntervalL2) (c : ℂ) (U : ℝ → ℂ)
    (hU : AbsolutelyContinuousOnInterval U 0 1) (hUc : Continuous U)
    (hU₂ : MemLp (deriv U) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hu : u =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] U)
    (himage : (fun s => deriv U s+U s^2-c) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] b)
    (hUend : U 1 = U 0) (y φ : Curve ℂ)
    (hy : AbsolutelyContinuousOnInterval (extend y) 0 1)
    (hφ : AbsolutelyContinuousOnInterval (extend φ) 0 1)
    (hy₂ : MemLp (deriv (extend y)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hφ₂ : MemLp (deriv (extend φ)) 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hend : extend y 1*extend φ 1 = extend y 0*extend φ 0) :
    shiftedMiuraWeakForm u c y φ = physicalL2HillWeakForm b y φ := by
  let g := y*φ
  have hg := absolutelyContinuous_curve_mul y φ hy hφ
  have hg₂ := memLp_deriv_curve_mul y φ hy hφ hy₂ hφ₂
  have hgi := intervalIntegrable_of_memLp_two hg₂
  have hUi := intervalIntegrable_of_memLp_two hU₂
  have hkin : IntervalIntegrable (fun s => deriv (extend y) s*deriv (extend φ) s) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      ((show MemLp (fun s => deriv (extend y) s*deriv (extend φ) s)
        1 (volume.restrict (Ioc (0 : ℝ) 1)) from hφ₂.mul hy₂).integrable le_rfl)
  have hcross := hgi.continuousOn_mul hU.continuousOn
  have hsquare : IntervalIntegrable (fun s => U s^2*extend g s) volume 0 1 :=
    ((hUc.pow 2).mul (continuous_extend g)).intervalIntegrable 0 1
  have hdu := hUi.mul_continuousOn (continuous_extend g).continuousOn
  have hcg := ((continuous_extend g).intervalIntegrable (μ := volume) 0 1).const_mul c
  have hpoly : (∫ s in (0 : ℝ)..1, (deriv (extend y) s-u s*extend y s)*
      (deriv (extend φ) s-u s*extend φ s)) =
      (∫ s in (0 : ℝ)..1, deriv (extend y) s*deriv (extend φ) s)-
        (∫ s in (0 : ℝ)..1, U s*deriv (extend g) s)+(∫ s in (0 : ℝ)..1, U s^2*extend g s) := by
    calc
      _ = ∫ s in (0 : ℝ)..1, (deriv (extend y) s*deriv (extend φ) s-
          U s*deriv (extend g) s)+U s^2*extend g s := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        filter_upwards [hu,ae_deriv_curve_mul y φ hy hφ] with s hs hd
        change deriv (extend g) s = _ at hd
        rw [hs,hd]
        change _ = _+U s^2*(extend y s*extend φ s)
        ring
      _ = _ := by rw [intervalIntegral.integral_add (hkin.sub hcross) hsquare,
        intervalIntegral.integral_sub hkin hcross]
  have hpot : (∫ s in (0 : ℝ)..1, b s*extend g s) =
      (∫ s in (0 : ℝ)..1, deriv U s*extend g s)+(∫ s in (0 : ℝ)..1, U s^2*extend g s)-
        c*(∫ s in (0 : ℝ)..1, extend g s) := by
    calc
      _ = ∫ s in (0 : ℝ)..1, (deriv U s*extend g s+U s^2*extend g s)-c*extend g s := by
        apply intervalIntegral.integral_congr_ae_restrict
        rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
        filter_upwards [himage] with s hs
        rw [← hs]
        ring
      _ = _ := by rw [intervalIntegral.integral_sub (hdu.add hsquare) hcg,
        intervalIntegral.integral_add hdu hsquare,intervalIntegral.integral_const_mul]
  have hip := integral_mul_deriv_eq_complex hU hg hUi hgi
  have hboundary : U 1*extend g 1-U 0*extend g 0 = 0 := by
    change U 1*(extend y 1*extend φ 1)-U 0*(extend y 0*extend φ 0) = 0
    rw [hUend,hend,sub_self]
  rw [hboundary,zero_sub] at hip
  change (∫ s in (0 : ℝ)..1, (deriv (extend y) s-u s*extend y s)*
      (deriv (extend φ) s-u s*extend φ s))-c*(∫ s in (0 : ℝ)..1, extend g s) =
      (∫ s in (0 : ℝ)..1, deriv (extend y) s*deriv (extend φ) s)+(∫ s in (0 : ℝ)..1, b s*extend g s)
  rw [hpoly,hip,hpot]
  ring

end NLS.MKdV
