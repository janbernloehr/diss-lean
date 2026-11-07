import NLS.KdV.HillNativeMidpointStationarity
import NLS.KdV.HillNativeConstantShiftLabels
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! The ACTUAL canonical periodic energy-midpoint derivative at the free
potential is EXACTLY the mean coefficient in every complex native source
direction. The proof combines mean-zero stationarity with actual full-label
constant-potential translation, including every low and collapsed pair. -/
noncomputable section
open scoped ComplexConjugate
open Set Complex Filter Topology NLS.ZakharovShabat
namespace NLS.KdV

theorem hillHminusCanonicalEnergyMidpoint_add_constant_real (n : ℕ+)
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (c : ℝ) :
    hillHminusCanonicalEnergyMidpoint n (q+periodOneConstantCLM (c:ℂ)) =
      hillHminusCanonicalEnergyMidpoint n q+(c:ℂ) := by
  have hs : IsRealPeriodOneHminusOne (q+periodOneConstantCLM (c:ℂ)) := by
    intro k
    change q.val (-k)+(periodOneConstantCLM (c:ℂ)).val (-k) =
      conj (q.val k+(periodOneConstantCLM (c:ℂ)).val k)
    rw [map_add,hr k,(isReal_periodOneConstantCLM c) k]
  rw [hillHminusCanonicalEnergyMidpoint_real n _ hs,hillHminusCanonicalEnergyMidpoint_real n q hr,
    hillHminusLabels_add_constant q hr c hs]
  simp only [Complex.ofReal_add]
  ring

theorem hillHminusCanonicalEnergyMidpoint_constant_real (n : ℕ+) (c : ℝ) :
    hillHminusCanonicalEnergyMidpoint n (periodOneConstantCLM (c:ℂ)) =
      hillHminusCanonicalEnergyMidpoint n 0+(c:ℂ) := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  simpa only [zero_add] using hillHminusCanonicalEnergyMidpoint_add_constant_real n 0 hr c

theorem fderiv_hillHminusCanonicalEnergyMidpoint_zero_constant (n : ℕ+) :
    (fderiv ℂ (hillHminusCanonicalEnergyMidpoint n) 0) (periodOneConstantCLM 1)=1 := by
  have hr : IsRealPeriodOneHminusOne (0 : PeriodOneHminusOne) := by intro k; simp
  have h0 := real_mem_hillHminusCanonicalZeroSequenceDomain 0 hr
  have hM := (analyticOnNhd_hillHminusCanonicalEnergyMidpoint n 0 h0).differentiableAt.hasFDerivAt
  have hi : HasDerivAt (fun t : ℝ => periodOneConstantCLM (t:ℂ)) (periodOneConstantCLM 1) 0 := by
    have hd := (periodOneConstantCLM.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
      (0:ℝ) Complex.ofRealCLM.hasDerivAt
    simpa only [Function.comp_def,ContinuousLinearMap.coe_restrictScalars',Complex.ofRealCLM_apply,
      Complex.ofReal_one] using! hd
  have hMr : HasFDerivAt (hillHminusCanonicalEnergyMidpoint n)
      ((fderiv ℂ (hillHminusCanonicalEnergyMidpoint n) 0).restrictScalars ℝ)
      ((fun t : ℝ => periodOneConstantCLM (t:ℂ)) 0) := by
    simpa only [Complex.ofReal_zero,map_zero] using hM.restrictScalars ℝ
  have hd := hMr.comp_hasDerivAt (0:ℝ) hi
  change HasDerivAt (fun t : ℝ => hillHminusCanonicalEnergyMidpoint n (periodOneConstantCLM (t:ℂ)))
    ((fderiv ℂ (hillHminusCanonicalEnergyMidpoint n) 0) (periodOneConstantCLM 1)) 0 at hd
  have he : (fun t : ℝ => hillHminusCanonicalEnergyMidpoint n (periodOneConstantCLM (t:ℂ))) =
      fun (t : ℝ) => hillHminusCanonicalEnergyMidpoint n 0+(t:ℂ) :=
    funext (hillHminusCanonicalEnergyMidpoint_constant_real n)
  rw [he] at hd
  have hlin : HasDerivAt (fun t : ℝ => hillHminusCanonicalEnergyMidpoint n 0+(t:ℂ)) (1:ℂ) 0 := by
    simpa only [Complex.ofRealCLM_apply,Complex.ofReal_one] using!
      Complex.ofRealCLM.hasDerivAt.const_add (hillHminusCanonicalEnergyMidpoint n 0)
  exact hd.unique hlin

theorem fderiv_hillHminusCanonicalEnergyMidpoint_zero_apply (n : ℕ+) (h : PeriodOneHminusOne) :
    (fderiv ℂ (hillHminusCanonicalEnergyMidpoint n) 0) h=h.val 0 := by
  have hm : (h-periodOneConstantCLM (h.val 0)).val 0=0 := by
    change h.val 0-(periodOneConstantCLM (h.val 0)).val 0=0
    simp [periodOneConstantCLM_apply]
  have hz := fderiv_hillHminusCanonicalEnergyMidpoint_zero_mean_zero n _ hm
  have hc : periodOneConstantCLM (h.val 0) = h.val 0 • periodOneConstantCLM 1 := by
    simpa only [smul_eq_mul,mul_one] using map_smul periodOneConstantCLM (h.val 0) (1:ℂ)
  rw [map_sub,hc,map_smul,smul_eq_mul,fderiv_hillHminusCanonicalEnergyMidpoint_zero_constant,mul_one] at hz
  exact sub_eq_zero.mp hz

theorem fderiv_hillHminusCanonicalEnergyMidpoint_zero (n : ℕ+) :
    fderiv ℂ (hillHminusCanonicalEnergyMidpoint n) 0 =
      WeightedCoeff.evalCLM (Weight.sobolev (-1)) 2 0 := by
  ext h
  exact fderiv_hillHminusCanonicalEnergyMidpoint_zero_apply n h

end NLS.KdV
