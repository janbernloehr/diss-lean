import NLS.KdV.HillIntrinsicPeriodRootJacobian
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



def hillAbelianNumeratorRootVariation (n : ℕ) (a h : Coeff 2) (E : ℂ) : ℂ :=
  fderiv ℂ (hillAbelianHilbertPsi n) (E,a) (0,h)

theorem analyticOnNhd_hillAbelianNumeratorRootVariation (n : ℕ) (a h : Coeff 2) :
    AnalyticOnNhd ℂ (hillAbelianNumeratorRootVariation n a h) univ := by
  intro E _
  have hd := (analyticOnNhd_hillAbelianHilbertPsi n (E,a) (mem_univ _)).fderiv
  have hc : AnalyticAt ℂ (fun E : ℂ => fderiv ℂ (hillAbelianHilbertPsi n) (E,a)) E :=
    hd.comp (f := fun E : ℂ => (E,a)) (analyticAt_id.prod analyticAt_const)
  let ev : ((ℂ × Coeff 2) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (0,h)
  exact (ev.analyticAt _).comp hc

theorem hillAbelianNumeratorRootVariation_eq_fderiv (n : ℕ) (a h : Coeff 2) (E : ℂ) :
    hillAbelianNumeratorRootVariation n a h E = fderiv ℂ (fun b : Coeff 2 => hillAbelianHilbertPsi n (E,b)) a h := by
  have hi : HasFDerivAt (fun b : Coeff 2 => (E,b)) (ContinuousLinearMap.inr ℂ ℂ (Coeff 2)) a :=
    hasFDerivAt_prodMk_right E a
  have hd := (analyticOnNhd_hillAbelianHilbertPsi n (E,a) (mem_univ _)).differentiableAt.hasFDerivAt.comp a hi
  exact (congrArg (fun T : Coeff 2 →L[ℂ] ℂ => T h) hd.fderiv).symm

theorem hillAbelianNumeratorRootVariation_single
    (n m : ℕ) (hm : 1 ≤ m) (hmn : m ≠ n) (a : Coeff 2) (E : ℂ) :
    hillAbelianNumeratorRootVariation n a (lp.single 2 (m : ℤ) 1) E =
      (m : ℂ)*hillAbelianRootSlope n m E a := by
  rw [hillAbelianNumeratorRootVariation_eq_fderiv]
  let S := lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 (m : ℤ)
  have hc : HasDerivAt (fun s : ℂ => a+lp.single 2 (m : ℤ) s) (lp.single 2 (m : ℤ) 1) 0 := by
    convert! (S.hasFDerivAt (x := (0 : ℂ))).hasDerivAt.const_add a using 1
  have hf : HasFDerivAt (fun b : Coeff 2 => hillAbelianHilbertPsi n (E,b))
      (fderiv ℂ (fun b : Coeff 2 => hillAbelianHilbertPsi n (E,b)) a) (a+lp.single 2 (m : ℤ) (0 : ℂ)) := by
    have hcomp := (analyticOnNhd_hillAbelianHilbertPsi n (E,a) (mem_univ _)).comp
      (f := fun b : Coeff 2 => (E,b)) (analyticAt_const.prod analyticAt_id)
    have hf0 : HasFDerivAt (fun b : Coeff 2 => hillAbelianHilbertPsi n (E,b))
        (fderiv ℂ (fun b : Coeff 2 => hillAbelianHilbertPsi n (E,b)) a) a := by
      convert! hcomp.differentiableAt.hasFDerivAt using 1
    simpa only [lp.single_zero,add_zero] using hf0
  have hd := hf.comp_hasDerivAt 0 hc
  have he : (fun s : ℂ => hillAbelianHilbertPsi n (E,a+lp.single 2 (m : ℤ) s)) =
      (fun s : ℂ => hillAbelianHilbertPsi n (E,a)+(m : ℂ)*s*hillAbelianRootSlope n m E a) :=
    funext (fun s => hillAbelianHilbertPsi_add_single n m hm hmn E a s)
  have hknown : HasDerivAt (fun s : ℂ => hillAbelianHilbertPsi n (E,a+lp.single 2 (m : ℤ) s))
      ((m : ℂ)*hillAbelianRootSlope n m E a) 0 := by
    rw [he]
    convert! (((hasDerivAt_id (0 : ℂ)).const_mul (m : ℂ)).mul_const
      (hillAbelianRootSlope n m E a)).const_add (hillAbelianHilbertPsi n (E,a)) using 1
    simp only [mul_one]
  exact hd.unique hknown

end NLS.KdV
