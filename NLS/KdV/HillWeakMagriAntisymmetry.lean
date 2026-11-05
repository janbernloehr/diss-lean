import NLS.KdV.HillGradientSecondRegularity
import NLS.KdV.HillWeakGradientMagri

/-! # Antisymmetry of the physical weak Magri pairing at periodic H² traces

The exact boundary product is retained until periodic first-derivative
traces cancel it. The potential itself is L² and is never differentiated.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem intervalIntegrable_weakGradientMagri_integrand (q : Coeff 2)
    (f df : Curve ℂ) (ddf : ℝ → ℂ) (g dg : Curve ℂ)
    (hddf : MemLp ddf 2 (volume.restrict (Ioc (0 : ℝ) 1))) :
    IntervalIntegrable (fun x => -ddf x*extend dg x+
      2*hillIntervalPotential q x*(extend f x*extend dg x-extend df x*extend g x)) volume 0 1 := by
  have hF : IntervalIntegrable ddf volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr (hddf.integrable (by norm_num))
  have hq : IntervalIntegrable (hillIntervalPotential q) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr
      ((memLp_hillIntervalPotential q).integrable (by norm_num))
  exact (hF.neg.mul_continuousOn (continuous_extend dg).continuousOn).add
    ((hq.const_mul 2).mul_continuousOn (((continuous_extend f).mul (continuous_extend dg)).sub
      ((continuous_extend df).mul (continuous_extend g))).continuousOn)

theorem hillWeakGradientMagri_antisymm (q : Coeff 2)
    (f df : Curve ℂ) (ddf : ℝ → ℂ) (g dg : Curve ℂ) (ddg : ℝ → ℂ)
    (hf : AbsolutelyContinuousOnInterval (extend df) 0 1)
    (hg : AbsolutelyContinuousOnInterval (extend dg) 0 1)
    (hddf : MemLp ddf 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hddg : MemLp ddg 2 (volume.restrict (Ioc (0 : ℝ) 1)))
    (hdf : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt (extend df) (ddf x) x)
    (hdg : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt (extend dg) (ddg x) x)
    (htrace : extend df 1*extend dg 1 = extend df 0*extend dg 0) :
    hillWeakGradientMagri q f df ddf g dg = -hillWeakGradientMagri q g dg ddg f df := by
  have hFi : IntervalIntegrable ddf volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr (hddf.integrable (by norm_num))
  have hGi : IntervalIntegrable ddg volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1)).mpr (hddg.integrable (by norm_num))
  have hi : IntervalIntegrable (fun x => ddf x*extend dg x+extend df x*ddg x) volume 0 1 :=
    (hFi.mul_continuousOn (continuous_extend dg).continuousOn).add
      (hGi.continuousOn_mul (continuous_extend df).continuousOn)
  have hac : AbsolutelyContinuousOnInterval (fun x => extend df x*extend dg x) 0 1 := by
    convert! hf.smul hg using 1
  have hd : ∀ᵐ x : ℝ ∂volume, x ∈ uIcc (0 : ℝ) 1 →
      HasDerivAt (fun r => extend df r*extend dg r) (ddf x*extend dg x+extend df x*ddg x) x := by
    rw [ae_restrict_iff' measurableSet_Ioc] at hdf hdg
    filter_upwards [hdf,hdg,Measure.ae_ne volume (0 : ℝ)] with x hx hy hn hmem
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hmem
    have hm : x ∈ Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hmem.1 (Ne.symm hn),hmem.2⟩
    exact (hx hm).mul (hy hm)
  have hFTC := integral_eq_sub_of_ac_of_ae_hasDerivAt hac hi hd
  rw [htrace,sub_self] at hFTC
  have hsum : hillWeakGradientMagri q f df ddf g dg+hillWeakGradientMagri q g dg ddg f df =
      -(∫ x in (0 : ℝ)..1,ddf x*extend dg x+extend df x*ddg x) := by
    rw [hillWeakGradientMagri,hillWeakGradientMagri,
      ← intervalIntegral.integral_add (intervalIntegrable_weakGradientMagri_integrand q f df ddf g dg hddf)
        (intervalIntegrable_weakGradientMagri_integrand q g dg ddg f df hddg),
      ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _
    ring
  rw [hFTC,neg_zero] at hsum
  linear_combination hsum

end NLS.KdV
