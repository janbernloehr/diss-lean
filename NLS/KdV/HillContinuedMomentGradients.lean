import NLS.KdV.HillEnergyGradientContours
import NLS.KdV.HillL2HighGapMoments
import NLS.ComplexAnalysis.TracePrimitiveMomentDifferential

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



def hillContinuedMomentGradientWeight (q : Coeff 2) (m : ℕ) (z : ℂ) : ℂ :=
  -(Real.pi : ℂ)⁻¹*z^m*(hillL2ContinuedRoot (z,q))⁻¹

def hillContinuedMomentGradient (q : Coeff 2) (c : ℂ) (r : ℝ) (m : ℕ) : Curve ℂ :=
  hillEnergyGradientContour q (hillContinuedMomentGradientWeight q m) c r

theorem continuousOn_hillContinuedMomentGradientWeight
    (q : Coeff 2) (c : ℂ) (r : ℝ) (m : ℕ)
    (hc : ∀ z∈sphere c r, (z,q)∈hillL2ContinuationDomain) :
    ContinuousOn (hillContinuedMomentGradientWeight q m) (sphere c r) := by
  have hroot : ContinuousOn (fun z => hillL2ContinuedRoot (z,q)) (sphere c r) :=
    analyticOnNhd_hillL2ContinuedRoot.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn hc
  exact (continuousOn_const.mul (continuousOn_id.pow m)).mul
    (hroot.inv₀ (fun z hz => hillL2ContinuedRoot_ne_zero (z,q) (hc z hz)))

/-- The actual normalized primitive moment has this physical L2
cotangent, with no change to its Arnold contour normalization. -/
theorem hillContinuedMomentGradient_represents_potential
    (q h : Coeff 2) (c : ℂ) (r : ℝ) (hr : 0≤r) (m : ℕ)
    (hc : ∀ z∈sphere c r, (z,q)∈hillL2ContinuationDomain) :
    (fderiv ℂ (hillL2SourceFamily.contourMoment c r m) q) h=
      hillPhysicalDirectionPairing h (hillContinuedMomentGradient q c r m) := by
  rw [hillL2SourceFamily.fderiv_contourMoment_apply c r hr m q h hc]
  rw [hillContinuedMomentGradient,hillEnergyGradientContour,
    map_circleIntegral (hillPhysicalDirectionPairing h)
      (circleIntegrable_hillEnergyGradientContour_integrand q (hillContinuedMomentGradientWeight q m)
        c r hr (continuousOn_hillContinuedMomentGradientWeight q c r m hc))]
  simp only [map_smul,smul_eq_mul]
  simp_rw [← hillEnergyDiscriminantGradient_represents_potential q h]
  rw [← circleIntegral.integral_const_mul]
  apply circleIntegral.integral_congr hr
  intro z _
  change -(Real.pi : ℂ)⁻¹*(z^m*(hillL2ContinuedRoot (z,q))⁻¹*
    ((fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p z) q) h))=
    hillContinuedMomentGradientWeight q m z*((fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p z) q) h)
  dsimp only [hillContinuedMomentGradientWeight]
  ring

theorem hillContinuedMomentGradient_H1
    (q : Coeff 2) (c : ℂ) (r : ℝ) (hr : 0≤r) (m : ℕ)
    (hc : ∀ z∈sphere c r, (z,q)∈hillL2ContinuationDomain) :
    AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (hillContinuedMomentGradient q c r m)) 0 1 ∧
      MemLp (NLS.LinearVolterra.extend (hillContinuedMomentGradient q c r m)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) ∧
      MemLp (deriv (NLS.LinearVolterra.extend (hillContinuedMomentGradient q c r m))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
  hillEnergyGradientContour_H1 q (hillContinuedMomentGradientWeight q m) c r hr
    (continuousOn_hillContinuedMomentGradientWeight q c r m hc)

theorem hillContinuedMomentGradients_GardnerBracket_eq_zero
    (q : Coeff 2) (c d : ℂ) (r s : ℝ) (hr : 0≤r) (hs : 0≤s) (m k : ℕ)
    (hc : ∀ z∈sphere c r, (z,q)∈hillL2ContinuationDomain)
    (hd : ∀ z∈sphere d s, (z,q)∈hillL2ContinuationDomain) :
    (∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillContinuedMomentGradient q c r m) x*
      deriv (NLS.LinearVolterra.extend (hillContinuedMomentGradient q d s k)) x)=0 :=
  hillEnergyGradientContour_GardnerBracket_eq_zero q
    (hillContinuedMomentGradientWeight q m) (hillContinuedMomentGradientWeight q k) c d r s hr hs
    (continuousOn_hillContinuedMomentGradientWeight q c r m hc)
    (continuousOn_hillContinuedMomentGradientWeight q d s k hd)

theorem hillL2HighContourMoment_gradient
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (n : ℕ) (hn : 1≤n) (hcut : 8*‖q‖≤(n : ℝ)) (m : ℕ) (h : Coeff 2) :
    (fderiv ℂ (hillL2HighContourMoment n m) (SpectralWeight.one.toCoeff q)) h=
      hillPhysicalDirectionPairing h (hillContinuedMomentGradient (SpectralWeight.one.toCoeff q)
        (freeHillValue n : ℂ) (n : ℝ) m) :=
  hillContinuedMomentGradient_represents_potential (SpectralWeight.one.toCoeff q) h
    (freeHillValue n : ℂ) (n : ℝ) (by positivity) m
    (mem_hillL2ContinuationDomain_high_sphere q hq n hn hcut)

/-- At every real source, the actual Arnold action tails have analytic
germs whose genuine source derivatives are the constructed physical cotangents. -/
theorem exists_hillRealHighActions_analytic_gradient_germs
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hqreal : IsRealHillPotential (SpectralWeight.one.toCoeff q)) :
    ∃ N : ℕ, 2≤N ∧ ∃ V : Set RealPeriodOneHillPotential,
      IsOpen V ∧ (⟨q,hq,hqreal⟩ : RealPeriodOneHillPotential)∈V ∧
      ∀ n : ℕ, N≤n →
      AnalyticAt ℂ (hillL2HighContourMoment n 0) (SpectralWeight.one.toCoeff q) ∧
      (∀ h : Coeff 2, (fderiv ℂ (hillL2HighContourMoment n 0) (SpectralWeight.one.toCoeff q)) h=
        hillPhysicalDirectionPairing h (hillContinuedMomentGradient (SpectralWeight.one.toCoeff q)
          (freeHillValue n : ℂ) (n : ℝ) 0)) ∧
      ∀ r∈V, hillL2HighContourMoment n 0 (SpectralWeight.one.toCoeff r.val)=
        (hillRealGapIntegral r.val r.property.1 r.property.2 n 0 : ℂ) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (8*‖q‖+2)
  have hN2 : 2≤N := by
    have hqnorm := norm_nonneg q
    by_contra h
    have hsmall : (N : ℝ)≤1 := by exact_mod_cast (show N≤1 by omega)
    linarith
  let V : Set RealPeriodOneHillPotential := {r | 8*‖r.val‖<(N : ℝ)}
  have hV : IsOpen V := isOpen_lt (continuous_subtype_val.norm.const_mul 8) continuous_const
  have hqV : (⟨q,hq,hqreal⟩ : RealPeriodOneHillPotential)∈V := by change 8*‖q‖<(N : ℝ);linarith
  refine ⟨N,hN2,V,hV,hqV,?_⟩
  intro n hn
  have hn2 : 2≤n := hN2.trans hn
  have hlt : 8*‖q‖<(n : ℝ) := by
    have hh : (N : ℝ)≤n := by exact_mod_cast hn
    linarith
  refine ⟨analyticAt_hillL2HighContourMoment q hq n (by omega) hlt.le 0,
    (fun h => hillL2HighContourMoment_gradient q hq n (by omega) hlt.le 0 h),?_⟩
  intro r hr
  have hcutr : 8*‖r.val‖≤(n : ℝ) :=
    (show 8*‖r.val‖<(N : ℝ) from hr).le.trans (by exact_mod_cast hn)
  exact hillL2HighContourMoment_eq_gapIntegral r.val r.property.1 r.property.2 n hn2 hcutr 0

end NLS.KdV
