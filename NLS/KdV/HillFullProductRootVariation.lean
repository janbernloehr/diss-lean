import NLS.KdV.HillFullProductUniformLimit
import NLS.KdV.HillRootSlopeNonvanishing
import Mathlib.Analysis.Calculus.FDeriv.Analytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The actual full-product variation in a root direction. -/
def hillFullProductRootVariation (a h : Coeff 2) (E : ℂ) : ℂ :=
  fderiv ℂ (hillAbelianHilbertProduct 0) (E,a) (0,h)

theorem analyticOnNhd_hillFullProductRootVariation (a h : Coeff 2) :
    AnalyticOnNhd ℂ (hillFullProductRootVariation a h) univ := by
  intro E _
  have hd := (analyticOnNhd_hillAbelianHilbertProduct 0 (E,a) (mem_univ _)).fderiv
  have hc := hd.comp (f := fun E : ℂ => (E,a)) (analyticAt_id.prod analyticAt_const)
  let ev : ((ℂ × Coeff 2) →L[ℂ] ℂ) →L[ℂ] ℂ := ContinuousLinearMap.apply ℂ ℂ (0,h)
  exact (ev.analyticAt _).comp hc

theorem hillFullProductRootVariation_eq_fderiv (a h : Coeff 2) (E : ℂ) :
    hillFullProductRootVariation a h E=fderiv ℂ (fun b : Coeff 2 => hillAbelianHilbertProduct 0 (E,b)) a h := by
  have hi : HasFDerivAt (fun b : Coeff 2 => (E,b)) (ContinuousLinearMap.inr ℂ ℂ (Coeff 2)) a :=
    hasFDerivAt_prodMk_right E a
  have hd := (analyticOnNhd_hillAbelianHilbertProduct 0 (E,a) (mem_univ _)).differentiableAt.hasFDerivAt.comp a hi
  exact (congrArg (fun T : Coeff 2 →L[ℂ] ℂ => T h) hd.fderiv).symm

/-- The full numerator with the original m-th root factor removed. -/
def hillFullProductRootSlope (m : ℕ) (E : ℂ) (a : Coeff 2) : ℂ :=
  hillAbelianHilbertProduct m (E,a)/(freeHillValue m : ℂ)

theorem hillAbelianFullProduct_eq_root_factor (m : ℕ) (hm : 1≤m) (E : ℂ) (a : Coeff 2) :
    hillAbelianHilbertProduct 0 (E,a)=(hillAbelianHilbertRootEnergy a m-E)*hillFullProductRootSlope m E a := by
  rw [hillAbelianHilbertProduct_full_factor m]
  have hf := hillAbelianComplexNumeratorFactor_eq_hilbert 0 (E,a) (m-1)
  rw [Nat.sub_add_cancel hm] at hf
  rw [←hf]
  have hm0 : m≠0 := by omega
  simp only [hillAbelianComplexNumeratorFactor,Nat.sub_add_cancel hm,if_neg hm0]
  dsimp only [hillFullProductRootSlope,hillAbelianHilbertRootEnergy]
  ring

theorem analyticOnNhd_hillFullProductRootSlope_roots (m : ℕ) (E : ℂ) :
    AnalyticOnNhd ℂ (hillFullProductRootSlope m E) univ := by
  intro a _
  exact ((analyticOnNhd_hillAbelianHilbertProduct m (E,a) (mem_univ _)).comp
    (f := fun a : Coeff 2 => (E,a)) (analyticAt_const.prod analyticAt_id)).div_const

theorem hillFullProductRootVariation_at_root (m : ℕ) (hm : 1≤m) (a h : Coeff 2) (E : ℂ)
    (hroot : hillAbelianHilbertRootEnergy a m=E) :
    hillFullProductRootVariation a h E=(m : ℂ)*h (m : ℤ)*hillFullProductRootSlope m E a := by
  have hfactor : (fun b : Coeff 2 => hillAbelianHilbertProduct 0 (E,b))=
      (fun b : Coeff 2 => (hillAbelianHilbertRootEnergy b m-E)*hillFullProductRootSlope m E b) :=
    funext (fun b => hillAbelianFullProduct_eq_root_factor m hm E b)
  have hL : HasFDerivAt (fun b : Coeff 2 => hillAbelianHilbertRootEnergy b m-E)
      ((m : ℂ) • lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (m : ℤ)) a := by
    convert! (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (m : ℤ)).hasFDerivAt (x := a)).const_mul
      (m : ℂ)).const_add (freeHillValue m : ℂ) |>.sub_const E using 1
  have hS := (analyticOnNhd_hillFullProductRootSlope_roots m E a (mem_univ _)).differentiableAt.hasFDerivAt
  have hd := hL.mul hS
  have hv := congrArg (fun T : Coeff 2 →L[ℂ] ℂ => T h) hd.fderiv
  simp only [Pi.mul_def] at hv
  rw [←hfactor] at hv
  rw [hillFullProductRootVariation_eq_fderiv]
  have heval : (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (m : ℤ)) h=h (m : ℤ) := rfl
  simpa only [smul_apply,smul_eq_mul,add_apply,ContinuousLinearMap.comp_apply,
    heval,hroot,sub_self,zero_mul,zero_add,add_zero,mul_comm,mul_left_comm,mul_assoc] using hv

/-- At an original gap-box vector the full root slope is nonzero on
the original m-th real spectral gap. -/
theorem hillFullProductRootSlope_ne_zero_on_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (roots : ℕ → ℝ) (hroots : roots∈hillGapRootBox q hq hr) (m : ℕ) (hm : 1≤m)
    (E : ℂ) (hE : E∈segment ℝ (hillRealLabels q hq hr (2*m-1) : ℂ) (hillRealLabels q hq hr (2*m) : ℂ)) :
    hillFullProductRootSlope m E (hillGapRootHilbertCoordinates q hq hr roots hroots)≠0 := by
  apply div_ne_zero _ (by simpa only [Nat.sub_add_cancel hm] using hillGapRootEnergyFactor_denominator_ne_zero (m-1))
  rw [hillAbelianHilbertProduct_eq_real_numerator m E _ roots
    (hillGapRootHilbertCoordinates_reconstruct q hq hr roots hroots),hillAbelianNumeratorProduct_ne_zero_iff q hq hr roots hroots]
  intro j hjm he
  have hx := re_mem_Icc_of_mem_real_segment _ _ (monotone_hillRealLabels q hq hr (by omega : 2*m-1≤2*m)) E hE
  have heR : roots j=E.re := by simpa only [ofReal_re] using congrArg Complex.re he
  have hroot := hroots j
  rcases hillRealGap_exterior_to_other_gap q hq hr m (j+1) hm (by omega) hjm E.re hx with hl | hu
  · linarith [hroot.1]
  · linarith [hroot.2]

end NLS.KdV
