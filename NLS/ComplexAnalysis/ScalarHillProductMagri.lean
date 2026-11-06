import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity
import NLS.FunctionalAnalysis.LinearVolterra
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Weak Magri reduction for products of rough Hill solutions

Only the potential itself is used. Products of two solutions at energy
mu obey a weak Lenard identity with an explicit endpoint term. No
spatial derivative of a rough potential is assumed.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.ComplexAnalysis

def scalarHillProductMagriIntegrand (q : ℝ → ℂ) (mu : ℂ)
    (A C : Curve (ℂ × ℂ)) (g dg : Curve ℂ) (x : ℝ) : ℂ :=
  -(2*(extend A x).2*(extend C x).2+2*(q x-mu)*(extend A x).1*(extend C x).1)*extend dg x+
    2*q x*((extend A x).1*(extend C x).1*extend dg x-
      ((extend A x).2*(extend C x).1+(extend A x).1*(extend C x).2)*extend g x)

theorem intervalIntegrable_scalarHillProductMagriIntegrand (q : ℝ → ℂ) (mu : ℂ)
    (A C : Curve (ℂ × ℂ)) (g dg : Curve ℂ)
    (hq : MemLp q 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    IntervalIntegrable (scalarHillProductMagriIntegrand q mu A C g dg) volume 0 1 := by
  have hA := continuous_extend A
  have hC := continuous_extend C
  have hg := continuous_extend g
  have hdg := continuous_extend dg
  have hqi : IntervalIntegrable q volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr (hq.integrable (by norm_num))
  have hdf : Continuous (fun x => (extend A x).2*(extend C x).1+(extend A x).1*(extend C x).2) :=
    (hA.snd.mul hC.fst).add (hA.fst.mul hC.snd)
  have hp : Continuous (fun x => 2*(mu*(extend A x).1*(extend C x).1-(extend A x).2*(extend C x).2)*extend dg x) :=
    ((((hA.fst.const_mul mu).mul hC.fst).sub (hA.snd.mul hC.snd)).const_mul 2).mul hdg
  have he : scalarHillProductMagriIntegrand q mu A C g dg = fun x =>
      2*(mu*(extend A x).1*(extend C x).1-(extend A x).2*(extend C x).2)*extend dg x-
        2*q x*((extend A x).2*(extend C x).1+(extend A x).1*(extend C x).2)*extend g x := by
    funext x
    unfold scalarHillProductMagriIntegrand
    ring
  rw [he]
  exact (hp.intervalIntegrable 0 1).sub
    ((((hqi.const_mul 2).mul_continuousOn hdf.continuousOn).mul_continuousOn hg.continuousOn))

theorem integral_scalarHillProductMagri_eq (q : ℝ → ℂ) (mu : ℂ)
    (A C : Curve (ℂ × ℂ)) (g dg : Curve ℂ)
    (hq : MemLp q 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hA : AbsolutelyContinuousOnInterval (extend A) 0 1)
    (hC : AbsolutelyContinuousOnInterval (extend C) 0 1)
    (hg : AbsolutelyContinuousOnInterval (extend g) 0 1)
    (hdA : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (fun r => (extend A r).1) (extend A x).2 x ∧
      HasDerivAt (fun r => (extend A r).2) ((q x-mu)*(extend A x).1) x)
    (hdC : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (fun r => (extend C r).1) (extend C x).2 x ∧
      HasDerivAt (fun r => (extend C r).2) ((q x-mu)*(extend C x).1) x)
    (hdg : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt (extend g) (extend dg x) x) :
    (∫ x in (0 : ℝ)..1,scalarHillProductMagriIntegrand q mu A C g dg x) =
      4*mu*(∫ x in (0 : ℝ)..1,(extend A x).1*(extend C x).1*extend dg x)-
        2*(((extend A 1).2*(extend C 1).2+mu*(extend A 1).1*(extend C 1).1)*extend g 1-
          ((extend A 0).2*(extend C 0).2+mu*(extend A 0).1*(extend C 0).1)*extend g 0) := by
  let f (x : ℝ) := (extend A x).1*(extend C x).1
  let df (x : ℝ) := (extend A x).2*(extend C x).1+(extend A x).1*(extend C x).2
  let K (x : ℝ) := (extend A x).2*(extend C x).2+mu*(extend A x).1*(extend C x).1
  have hAf := absolutelyContinuousOnInterval_clm hA (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hAd := absolutelyContinuousOnInterval_clm hA (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have hCf := absolutelyContinuousOnInterval_clm hC (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hCd := absolutelyContinuousOnInterval_clm hC (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have hK : AbsolutelyContinuousOnInterval K 0 1 := by
    convert! (hAd.smul hCd).add ((hAf.const_smul mu).smul hCf) using 1
  have hKg : AbsolutelyContinuousOnInterval (fun x => K x*extend g x) 0 1 := by
    convert! hK.smul hg using 1
  have hAc := continuous_extend A
  have hCc := continuous_extend C
  have hdf : Continuous df := (hAc.snd.mul hCc.fst).add (hAc.fst.mul hCc.snd)
  have hKc : Continuous K := (hAc.snd.mul hCc.snd).add ((hAc.fst.const_mul mu).mul hCc.fst)
  have hf : Continuous f := hAc.fst.mul hCc.fst
  have hqi : IntervalIntegrable q volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr (hq.integrable (by norm_num))
  have hL : IntervalIntegrable (fun x => q x*df x*extend g x+K x*extend dg x) volume 0 1 :=
    ((hqi.mul_continuousOn hdf.continuousOn).mul_continuousOn (continuous_extend g).continuousOn).add
      ((hKc.mul (continuous_extend dg)).intervalIntegrable 0 1)
  have hd : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (fun r => K r*extend g r) (q x*df x*extend g x+K x*extend dg x) x := by
    filter_upwards [hdA,hdC,hdg] with x hx hy hz
    have hk := (hx.2.mul hy.2).add (((hx.1.const_mul mu).mul hy.1))
    have hh := hk.mul hz
    convert! hh using 1
    dsimp only [K,df,Pi.add_apply,Pi.mul_apply]
    ring
  have hd' : ∀ᵐ x : ℝ, x ∈ uIcc (0 : ℝ) 1 →
      HasDerivAt (fun r => K r*extend g r) (q x*df x*extend g x+K x*extend dg x) x := by
    rw [ae_restrict_iff' measurableSet_Ioc] at hd
    have hn : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := Measure.ae_ne volume 0
    filter_upwards [hd,hn] with x hx hn hmem
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hmem
    exact hx ⟨lt_of_le_of_ne hmem.1 (Ne.symm hn),hmem.2⟩
  have hFTC := integral_eq_sub_of_ac_of_ae_hasDerivAt hKg hL hd'
  have he : scalarHillProductMagriIntegrand q mu A C g dg =
      fun x => 4*mu*(f x*extend dg x)-2*(q x*df x*extend g x+K x*extend dg x) := by
    funext x
    dsimp only [scalarHillProductMagriIntegrand,f,df,K]
    ring
  have hi : IntervalIntegrable (fun x => 4*mu*(f x*extend dg x)) volume 0 1 :=
    ((hf.mul (continuous_extend dg)).intervalIntegrable 0 1).const_mul (4*mu)
  have hj : IntervalIntegrable (fun x => 2*(q x*df x*extend g x+K x*extend dg x)) volume 0 1 := hL.const_mul 2
  calc
    _ = ∫ x in (0 : ℝ)..1,4*mu*(f x*extend dg x)-2*(q x*df x*extend g x+K x*extend dg x) := by
      apply intervalIntegral.integral_congr
      intro x _
      exact congrFun he x
    _ = _ := by
      rw [intervalIntegral.integral_sub hi hj,intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,hFTC]

end NLS.ComplexAnalysis
