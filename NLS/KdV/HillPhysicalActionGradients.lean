import NLS.KdV.HillRealSourceMomentGerms
import NLS.KdV.HillEnergyGradientContours

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



private theorem source_sub_fderiv
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : E → ℂ) (hF : AnalyticAt ℂ F 0) (q h : E) :
    (fderiv ℂ (fun p : E => F (p-q)) q) h=(fderiv ℂ F 0) h := by
  have hF' : AnalyticAt ℂ F (q-q) := by simpa only [sub_self] using hF
  have hf : HasFDerivAt (fun p : E => p-q) (ContinuousLinearMap.id ℂ E) q := (hasFDerivAt_id q).sub_const q
  have hd := hF'.differentiableAt.hasFDerivAt.comp q (f := fun p : E => p-q) hf
  simpa only [sub_self,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,Function.comp_def,id_eq] using
    congrArg (fun L : E →L[ℂ] ℂ => L h) hd.fderiv

private theorem source_add_fderiv
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : E → ℂ) (q : E) (hF : AnalyticAt ℂ F q) (h : E) :
    (fderiv ℂ (fun p : E => F (p+q)) 0) h=(fderiv ℂ F q) h := by
  have hF' : AnalyticAt ℂ F ((0 : E)+q) := by simpa only [zero_add] using hF
  have hd := hF'.differentiableAt.hasFDerivAt.comp 0 ((hasFDerivAt_id (0 : E)).add_const q)
  simpa only [zero_add,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,Function.comp_def,id_eq] using
    congrArg (fun L : E →L[ℂ] ℂ => L h) hd.fderiv

def hillPhysicalMomentGradientWeight (p : Coeff 2) (m : ℕ) (z : ℂ) : ℂ :=
  -(Real.pi : ℂ)⁻¹*z^m*(hillL2RealCutRoot p z)⁻¹

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The physical moment cotangent uses the original globally normalized
real-cut root on the intrinsic isolating circle of the chosen gap. -/
def hillPhysicalMomentGradient (n m : ℕ) : Curve ℂ :=
  hillEnergyGradientContour (SpectralWeight.one.toCoeff q)
    (hillPhysicalMomentGradientWeight (SpectralWeight.one.toCoeff q) m)
    (hillRealGapCenter q hq hr n : ℂ) (hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n)

theorem continuousOn_hillPhysicalMomentGradientWeight (n : ℕ) (hn : 1≤n) (m : ℕ) :
    ContinuousOn (hillPhysicalMomentGradientWeight (SpectralWeight.one.toCoeff q) m)
      (sphere (hillRealGapCenter q hq hr n : ℂ) (hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n)) := by
  have hP := (analyticOnNhd_hillL2RealCutPrimitive q hq hr).continuousOn.mono
    (hillRealGapContour_sphere_subset q hq hr n hn)
  have hroot := (Complex.continuous_sinh.comp_continuousOn hP).const_mul 2
  exact (continuousOn_const.mul (continuousOn_id.pow m)).mul (hroot.inv₀
    (fun z hz => hillL2RealCutRoot_ne_zero q hq hr z (hillRealGapContour_sphere_subset q hq hr n hn hz)))

/-- The germ matching the actual physical moment has this genuine
source derivative at every real base and every gap, including collapsed gaps. -/
theorem hillRealSourceMoment_gradient (n : ℕ) (hn : 1≤n) (m : ℕ) (h : Coeff 2) :
    (fderiv ℂ (hillRealSourceMoment q hq hr n m) (SpectralWeight.one.toCoeff q)) h=
      hillPhysicalDirectionPairing h (hillPhysicalMomentGradient q hq hr n m) := by
  let p0 := SpectralWeight.one.toCoeff q
  let c : ℂ := hillRealGapCenter q hq hr n
  let R := hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n
  let f := hillRecenteredTraceFamily q hq hr
  have hR : 0≤R := add_nonneg (hillRealGapContour_geometry q hq hr n hn).1
    (hillRealGapContour_geometry q hq hr n hn).2.1.le
  have hc (z : ℂ) (hz : z∈sphere c R) : (z,0)∈f.continuationDomain :=
    mem_hillRecenteredContinuationDomain_base q hq hr z (hillRealGapContour_sphere_subset q hq hr n hn hz)
  obtain ⟨V,_,h0V,hA⟩ := f.exists_analytic_contourMoment c R hR 0 hc m
  change (fderiv ℂ (fun p : Coeff 2 => f.contourMoment c R m (p-p0)) p0) h=_
  rw [source_sub_fderiv (f.contourMoment c R m) (hA 0 h0V) p0 h,
    f.fderiv_contourMoment_apply c R hR m 0 h hc]
  have htrace (z : ℂ) : (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant (p+p0) z) 0) h=
      (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p z) p0) h :=
    source_add_fderiv (fun p : Coeff 2 => hillL2Discriminant p z) p0
      ((analyticOnNhd_hillL2Discriminant_joint (z,p0) (mem_univ _)).comp
        (f := fun p : Coeff 2 => (z,p)) (analyticAt_const.prod analyticAt_id)) h
  change -(Real.pi : ℂ)⁻¹*(∮ z in C(c,R),z^m*(hillRecenteredRoot q hq hr (z,0))⁻¹*
    ((fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant (p+p0) z) 0) h))=_
  simp_rw [hillRecenteredRoot_base,htrace]
  rw [hillPhysicalMomentGradient,hillEnergyGradientContour,
    map_circleIntegral (hillPhysicalDirectionPairing h)
      (circleIntegrable_hillEnergyGradientContour_integrand p0 (hillPhysicalMomentGradientWeight p0 m)
        c R hR (continuousOn_hillPhysicalMomentGradientWeight q hq hr n hn m))]
  simp only [map_smul,smul_eq_mul]
  simp_rw [← hillEnergyDiscriminantGradient_represents_potential p0 h]
  rw [← circleIntegral.integral_const_mul]
  apply circleIntegral.integral_congr hR
  intro z _
  dsimp only [hillPhysicalMomentGradientWeight,p0]
  ring

theorem hillPhysicalMomentGradient_H1 (n : ℕ) (hn : 1≤n) (m : ℕ) :
    AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (hillPhysicalMomentGradient q hq hr n m)) 0 1 ∧
      MemLp (NLS.LinearVolterra.extend (hillPhysicalMomentGradient q hq hr n m)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) ∧
      MemLp (deriv (NLS.LinearVolterra.extend (hillPhysicalMomentGradient q hq hr n m))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  hillEnergyGradientContour_H1 (SpectralWeight.one.toCoeff q)
    (hillPhysicalMomentGradientWeight (SpectralWeight.one.toCoeff q) m)
    (hillRealGapCenter q hq hr n : ℂ) (hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n)
    (add_nonneg (hillRealGapContour_geometry q hq hr n hn).1 (hillRealGapContour_geometry q hq hr n hn).2.1.le)
    (continuousOn_hillPhysicalMomentGradientWeight q hq hr n hn m)

/-- All actual physical moment cotangents commute in the genuine
Gardner integral, at every pair of gaps and hierarchy levels. -/
theorem hillPhysicalMomentGradients_GardnerBracket_eq_zero
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (m l : ℕ) :
    (∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillPhysicalMomentGradient q hq hr n m) x*
      deriv (NLS.LinearVolterra.extend (hillPhysicalMomentGradient q hq hr k l)) x)=0 :=
  hillEnergyGradientContour_GardnerBracket_eq_zero (SpectralWeight.one.toCoeff q)
    (hillPhysicalMomentGradientWeight (SpectralWeight.one.toCoeff q) m)
    (hillPhysicalMomentGradientWeight (SpectralWeight.one.toCoeff q) l)
    (hillRealGapCenter q hq hr n : ℂ) (hillRealGapCenter q hq hr k : ℂ)
    (hillRealGapHalfLength q hq hr n+hillRealGapCollar q hq hr n)
    (hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k)
    (add_nonneg (hillRealGapContour_geometry q hq hr n hn).1 (hillRealGapContour_geometry q hq hr n hn).2.1.le)
    (add_nonneg (hillRealGapContour_geometry q hq hr k hk).1 (hillRealGapContour_geometry q hq hr k hk).2.1.le)
    (continuousOn_hillPhysicalMomentGradientWeight q hq hr n hn m)
    (continuousOn_hillPhysicalMomentGradientWeight q hq hr k hk l)

end NLS.KdV
