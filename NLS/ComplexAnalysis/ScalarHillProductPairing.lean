import NLS.ComplexAnalysis.ScalarHillProductMagri

/-! # A boundary formula for mixed squared-solution pairings

The identity uses actual absolutely continuous Hill solutions at two
energies. It retains the endpoint term needed for periodic trace gradients.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.FunctionalAnalysis
namespace NLS.ComplexAnalysis

theorem integral_scalarHill_squared_product_derivative
    (q : ℝ → ℂ) (mu E : ℂ) (A B C : Curve (ℂ × ℂ))
    (hA : AbsolutelyContinuousOnInterval (extend A) 0 1)
    (hB : AbsolutelyContinuousOnInterval (extend B) 0 1)
    (hC : AbsolutelyContinuousOnInterval (extend C) 0 1)
    (hdA : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (fun r => (extend A r).1) (extend A x).2 x ∧
      HasDerivAt (fun r => (extend A r).2) ((q x-mu)*(extend A x).1) x)
    (hdB : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (fun r => (extend B r).1) (extend B x).2 x ∧
      HasDerivAt (fun r => (extend B r).2) ((q x-E)*(extend B x).1) x)
    (hdC : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (fun r => (extend C r).1) (extend C x).2 x ∧
      HasDerivAt (fun r => (extend C r).2) ((q x-E)*(extend C x).1) x)
    (ha0 : (extend A 0).1 = 0) (ha1 : (extend A 1).1 = 0) :
    2*(mu-E)*(∫ x in (0 : ℝ)..1,(extend A x).1^2*
      ((extend B x).2*(extend C x).1+(extend B x).1*(extend C x).2)) =
        (extend A 1).2^2*(extend B 1).1*(extend C 1).1-
          (extend A 0).2^2*(extend B 0).1*(extend C 0).1 := by
  let W (Y : Curve (ℂ × ℂ)) (x : ℝ) :=
    (extend A x).1*(extend Y x).2-(extend A x).2*(extend Y x).1
  let H (x : ℝ) := W B x*W C x+(mu-E)*(extend A x).1^2*(extend B x).1*(extend C x).1
  let P (x : ℝ) := (extend A x).1^2*
    ((extend B x).2*(extend C x).1+(extend B x).1*(extend C x).2)
  have hAf := absolutelyContinuousOnInterval_clm hA (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hAd := absolutelyContinuousOnInterval_clm hA (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have hBf := absolutelyContinuousOnInterval_clm hB (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hBd := absolutelyContinuousOnInterval_clm hB (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have hCf := absolutelyContinuousOnInterval_clm hC (ContinuousLinearMap.fst ℝ ℂ ℂ)
  have hCd := absolutelyContinuousOnInterval_clm hC (ContinuousLinearMap.snd ℝ ℂ ℂ)
  have hH : AbsolutelyContinuousOnInterval H 0 1 := by
    convert! ((hAf.smul hBd).sub (hAd.smul hBf)).smul
      ((hAf.smul hCd).sub (hAd.smul hCf)) |>.add
        ((((hAf.smul hAf).const_smul (mu-E)).smul hBf).smul hCf) using 1
    funext x
    dsimp only [H,W,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,Pi.mul_apply,smul_eq_mul,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
    ring
  have hP : Continuous P := ((continuous_extend A).fst.pow 2).mul
    (((continuous_extend B).snd.mul (continuous_extend C).fst).add
      ((continuous_extend B).fst.mul (continuous_extend C).snd))
  have hd : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt H (2*(mu-E)*P x) x := by
    filter_upwards [hdA,hdB,hdC] with x ha hb hc
    have hwB : HasDerivAt (W B) ((mu-E)*(extend A x).1*(extend B x).1) x := by
      convert! ((ha.1.mul hb.2).sub (ha.2.mul hb.1)) using 1
      ring
    have hwC : HasDerivAt (W C) ((mu-E)*(extend A x).1*(extend C x).1) x := by
      convert! ((ha.1.mul hc.2).sub (ha.2.mul hc.1)) using 1
      ring
    have hh := (hwB.mul hwC).add ((((ha.1.pow 2).const_mul (mu-E)).mul hb.1).mul hc.1)
    convert! hh using 1
    dsimp only [H,P,W,Pi.add_apply,Pi.mul_apply,Pi.pow_apply]
    ring
  have hd' : ∀ᵐ x : ℝ, x ∈ uIcc (0 : ℝ) 1 → HasDerivAt H (2*(mu-E)*P x) x := by
    rw [ae_restrict_iff' measurableSet_Ioc] at hd
    filter_upwards [hd,Measure.ae_ne volume (0 : ℝ)] with x hx hx0 hm
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hm
    exact hx ⟨lt_of_le_of_ne hm.1 (Ne.symm hx0),hm.2⟩
  have hi := integral_eq_sub_of_ac_of_ae_hasDerivAt hH
    ((hP.const_mul (2*(mu-E))).intervalIntegrable 0 1) hd'
  rw [intervalIntegral.integral_const_mul] at hi
  calc
    _ = H 1-H 0 := hi
    _ = _ := by
      dsimp only [H,W]
      rw [ha0,ha1]
      ring


end NLS.ComplexAnalysis
