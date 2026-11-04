import NLS.KdV.HillLogNormingGardnerBrackets

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The opposite mixed bracket is obtained from the genuine H1
integration by parts, with vanishing Dirichlet and norming endpoints. -/
theorem hillLogDirichletGardnerBracket_eq
    (q : RealPeriodOneHillPotential) (n m : ℕ) (hn : 1≤n) (hm : 1≤m) :
    (∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn) x*
      deriv (NLS.LinearVolterra.extend (hillDirichletGradientCurve q m hm)) x)=
      if n=m then (1/2 : ℂ) else 0 := by
  let f := NLS.LinearVolterra.extend (hillLogNormingGradientCurve q n hn)
  let g := NLS.LinearVolterra.extend (hillDirichletGradientCurve q m hm)
  have hF := hillLogNormingGradient_H1 q n hn
  have hG := hillDirichletGradient_H1 q m hm
  have hf : IntervalIntegrable (deriv f) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤1)).mpr
      (hF.2.2.integrable (by norm_num))
  have hg : IntervalIntegrable (deriv g) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0 : ℝ)≤1)).mpr
      (hG.2.2.integrable (by norm_num))
  have hi := integral_mul_deriv_eq_complex hF.1 hG.1 hf hg
  have h0 : f 0=0 := by
    simpa only [f,NLS.LinearVolterra.extend,projIcc_of_mem _ (show (0 : ℝ)∈Icc 0 1 by norm_num)] using
      (hillLogNormingGradientCurve_endpoints q n hn).1
  have h1 : f 1=0 := by
    simpa only [f,NLS.LinearVolterra.extend,projIcc_of_mem _ (show (1 : ℝ)∈Icc 0 1 by norm_num)] using
      (hillLogNormingGradientCurve_endpoints q n hn).2
  change (∫ x in (0 : ℝ)..1,f x*deriv g x)=_
  change (∫ x in (0 : ℝ)..1,f x*deriv g x)=f 1*g 1-f 0*g 0-
    (∫ x in (0 : ℝ)..1,deriv f x*g x) at hi
  have hswap : (∫ x in (0 : ℝ)..1,deriv f x*g x)=hillDirichletLogGardnerBracket q m n hm hn := by
    apply intervalIntegral.integral_congr
    intro x _
    exact mul_comm _ _
  rw [hi,h0,h1,zero_mul,zero_mul,sub_self,zero_sub,hswap,hillDirichletLogGardnerBracket_eq]
  by_cases h : n=m
  · subst m
    norm_num
  · rw [if_neg h,if_neg (Ne.symm h),neg_zero]

private theorem integral_scaled_gardner_pairing
    (c d : ℂ) (f g : ℝ → ℂ) :
    (∫ x in (0 : ℝ)..1,(c*f x)*deriv (fun y => d*g y) x)=
      (c*d)*(∫ x in (0 : ℝ)..1,f x*deriv g x) := by
  rw [deriv_const_mul_field']
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  ring

/-- The genuine spectral cotangents with the norming coordinate scaled
by -2, so that its mixed Gardner bracket with the Dirichlet energy is 1. -/
def hillDirichletDarbouxGradient (q : RealPeriodOneHillPotential) (i : Bool × ℕ) : Curve ℂ :=
  if i.1 then (-2 : ℂ) • hillLogNormingGradientCurve q (i.2+1) (by omega)
  else hillDirichletGradientCurve q (i.2+1) (by omega)

/-- The complete canonical matrix for the actual spectral cotangents,
including the source normalization in both mixed directions. -/
theorem hillDirichletDarbouxGradient_pairing
    (q : RealPeriodOneHillPotential) (i j : Bool × ℕ) :
    (∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillDirichletDarbouxGradient q i) x*
      deriv (NLS.LinearVolterra.extend (hillDirichletDarbouxGradient q j)) x)=
      if i.1=j.1 then 0 else if i.2=j.2 then (if i.1 then -1 else 1) else 0 := by
  rcases i with ⟨b,n⟩
  rcases j with ⟨c,m⟩
  cases b <;> cases c
  · exact hillDirichletGardnerBracket_eq_zero q (n+1) (m+1) (by omega) (by omega)
  · change (∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillDirichletGradientCurve q (n+1) (by omega)) x*
      deriv (fun y => (-2 : ℂ)*NLS.LinearVolterra.extend (hillLogNormingGradientCurve q (m+1) (by omega)) y) x)=_
    have h := integral_scaled_gardner_pairing 1 (-2)
      (NLS.LinearVolterra.extend (hillDirichletGradientCurve q (n+1) (by omega)))
      (NLS.LinearVolterra.extend (hillLogNormingGradientCurve q (m+1) (by omega)))
    simp only [one_mul] at h
    rw [h]
    change (-2 : ℂ)*hillDirichletLogGardnerBracket q (n+1) (m+1) (by omega) (by omega)=_
    rw [hillDirichletLogGardnerBracket_eq]
    by_cases hnm : n=m
    · subst m;norm_num
    · simp [hnm]
  · change (∫ x in (0 : ℝ)..1,((-2 : ℂ)*NLS.LinearVolterra.extend (hillLogNormingGradientCurve q (n+1) (by omega)) x)*
      deriv (NLS.LinearVolterra.extend (hillDirichletGradientCurve q (m+1) (by omega))) x)=_
    have h := integral_scaled_gardner_pairing (-2) 1
      (NLS.LinearVolterra.extend (hillLogNormingGradientCurve q (n+1) (by omega)))
      (NLS.LinearVolterra.extend (hillDirichletGradientCurve q (m+1) (by omega)))
    simp only [one_mul,mul_one] at h
    rw [h,hillLogDirichletGardnerBracket_eq]
    by_cases hnm : n=m
    · subst m;norm_num
    · simp [hnm]
  · change (∫ x in (0 : ℝ)..1,((-2 : ℂ)*NLS.LinearVolterra.extend (hillLogNormingGradientCurve q (n+1) (by omega)) x)*
      deriv (fun y => (-2 : ℂ)*NLS.LinearVolterra.extend (hillLogNormingGradientCurve q (m+1) (by omega)) y) x)=_
    rw [integral_scaled_gardner_pairing]
    change ((-2 : ℂ)*(-2))*hillLogNormingGardnerBracket q (n+1) (m+1) (by omega) (by omega)=_
    rw [hillLogNormingGardnerBracket_eq_zero,mul_zero]
    rfl

end NLS.KdV
