import NLS.KdV.HillEntireNumeratorRootVariation
import NLS.KdV.HillRootSlopeNonvanishing

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



theorem hillAbelianHilbertPsi_eq_root_factor
    (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≠ n) (E : ℂ) (a : Coeff 2) :
    hillAbelianHilbertPsi n (E,a) =
      (hillAbelianHilbertRootEnergy a m-E)*hillAbelianRootSlope n m E a := by
  have h0 : hillAbelianRootUpdate m (a,hillAbelianHilbertRootEnergy a m) = a := by
    simpa only [mul_zero,add_zero,lp.single_zero] using hillAbelianRootUpdate_eq_add_single m hm a 0
  calc
    _ = hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (a,hillAbelianHilbertRootEnergy a m)) := by rw [h0]
    _ = _ := hillAbelianHilbertPsi_rootUpdate_eq_rootSlope n m hm hmn E a (hillAbelianHilbertRootEnergy a m)

theorem analyticOnNhd_hillAbelianRootSlope_roots (n m : ℕ) (E : ℂ) :
    AnalyticOnNhd ℂ (fun a : Coeff 2 => hillAbelianRootSlope n m E a) univ := by
  intro a _
  have hR : AnalyticAt ℂ (fun b : Coeff 2 => hillAbelianRootUpdate m (b,E+1)) a := by
    convert! (analyticOnNhd_hillAbelianRootUpdate m (a,E+1) (mem_univ _)).comp
      (f := fun b : Coeff 2 => (b,E+1)) (analyticAt_id.prod analyticAt_const) using 1
  have hJ : AnalyticAt ℂ (fun b : Coeff 2 => (E,hillAbelianRootUpdate m (b,E+1))) a :=
    analyticAt_const.prod hR
  exact (analyticOnNhd_hillAbelianHilbertPsi n (E,hillAbelianRootUpdate m (a,E+1)) (mem_univ _)).comp
    (f := fun b : Coeff 2 => (E,hillAbelianRootUpdate m (b,E+1))) hJ

theorem hillAbelianNumeratorRootVariation_at_root
    (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≠ n) (a h : Coeff 2) (E : ℂ)
    (hroot : hillAbelianHilbertRootEnergy a m = E) :
    hillAbelianNumeratorRootVariation n a h E =
      (m : ℂ)*h (m : ℤ)*hillAbelianRootSlope n m E a := by
  have hfactor : (fun b : Coeff 2 => hillAbelianHilbertPsi n (E,b)) =
      (fun b : Coeff 2 => (hillAbelianHilbertRootEnergy b m-E)*hillAbelianRootSlope n m E b) :=
    funext (fun b => hillAbelianHilbertPsi_eq_root_factor n m hm hmn E b)
  have hL : HasFDerivAt (fun b : Coeff 2 => hillAbelianHilbertRootEnergy b m-E)
      ((m : ℂ) • lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (m : ℤ)) a := by
    convert! (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (m : ℤ)).hasFDerivAt (x := a)).const_mul
      (m : ℂ)).const_add (freeHillValue m : ℂ) |>.sub_const E using 1
  have hS := ((analyticOnNhd_hillAbelianRootSlope_roots n m E) a (mem_univ _)).differentiableAt.hasFDerivAt
  have hd := hL.mul hS
  have hv := congrArg (fun T : Coeff 2 →L[ℂ] ℂ => T h) hd.fderiv
  simp only [Pi.mul_def] at hv
  rw [← hfactor] at hv
  rw [hillAbelianNumeratorRootVariation_eq_fderiv]
  have heval : (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (m : ℤ)) h = h (m : ℤ) := rfl
  simpa only [smul_apply,smul_eq_mul,add_apply,ContinuousLinearMap.comp_apply,
    heval,hroot,sub_self,zero_mul,zero_add,add_zero,mul_comm,mul_left_comm,mul_assoc] using hv

end NLS.KdV
