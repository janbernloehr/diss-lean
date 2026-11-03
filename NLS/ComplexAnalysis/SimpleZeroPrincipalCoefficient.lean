import NLS.ComplexAnalysis.CauchyFiniteHoles

/-! # The filled principal coefficient at a simple analytic zero -/
noncomputable section
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis

def simpleZeroPrincipalCoefficient (P f : ℂ → ℂ) (a z : ℂ) : ℂ := P z / dslope f a z

theorem simpleZeroPrincipalCoefficient_at_base (P f : ℂ → ℂ) (a : ℂ) :
    simpleZeroPrincipalCoefficient P f a a = P a / deriv f a := by
  simp only [simpleZeroPrincipalCoefficient,dslope_same]

theorem simpleZeroPrincipalCoefficient_eq_mul_sub (P f : ℂ → ℂ) (a : ℂ) (hf : f a = 0)
    (z : ℂ) (hz : z ≠ a) :
    simpleZeroPrincipalCoefficient P f a z = (z-a)*(P z/f z) := by
  simp only [simpleZeroPrincipalCoefficient,dslope_of_ne f hz,slope,smul_eq_mul,vsub_eq_sub,hf,sub_zero,
    div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

theorem analyticAt_simpleZeroPrincipalCoefficient (P f : ℂ → ℂ) (a : ℂ)
    (hP : AnalyticAt ℂ P a) (hf : AnalyticOnNhd ℂ f univ) (hd : deriv f a ≠ 0) :
    AnalyticAt ℂ (simpleZeroPrincipalCoefficient P f a) a := by
  have hs := analyticOnNhd_dslope_of_analytic f univ a hf (mem_univ _)
  exact hP.div (hs a (mem_univ _)) (by simpa only [dslope_same] using hd)

theorem tendsto_mul_sub_div_at_simple_zero (P f : ℂ → ℂ) (a : ℂ)
    (hP : AnalyticAt ℂ P a) (hf : AnalyticOnNhd ℂ f univ)
    (hzero : f a = 0) (hd : deriv f a ≠ 0) :
    Tendsto (fun z => (z-a)*(P z/f z)) (𝓝[≠] a) (𝓝 (P a/deriv f a)) := by
  have ht := ((analyticAt_simpleZeroPrincipalCoefficient P f a hP hf hd).continuousAt.tendsto).mono_left
    (show 𝓝[≠] a ≤ 𝓝 a from nhdsWithin_le_nhds)
  rw [simpleZeroPrincipalCoefficient_at_base] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact simpleZeroPrincipalCoefficient_eq_mul_sub P f a hzero z hz

end NLS.ComplexAnalysis
