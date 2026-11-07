import NLS.KdV.ClassicalHillTraceGradientBoundary
import NLS.ComplexAnalysis.ThirdOrderPeriodicLagrange

/-! The ACTUAL discriminant-gradient Gardner integral vanishes at every
continuous complex unit-period potential with an interior derivative.
The equal-energy case is treated separately; no division by an energy
difference, spectral gap or eigenfunction normalization is hidden. -/
noncomputable section
open Set Complex MeasureTheory NLS.LinearVolterra NLS.ComplexAnalysis
namespace NLS.KdV

theorem integral_classicalHillTraceGradients_eq_zero (q : Curve ℂ) (Qdot : ℝ → ℂ)
    (hq : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt (extend q) (Qdot t) t)
    (hperiod : extend q 1=extend q 0) (μ ν : ℂ) :
    (∫ x in (0:ℝ)..1, classicalHillTraceGradient q μ x*classicalHillTraceGradientPrime q ν x)=0 := by
  have hD (E : ℂ) (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      HasDerivAt (classicalHillTraceGradient q E) (classicalHillTraceGradientPrime q E t) t :=
    hasDerivAt_classicalHillTraceGradient q E ⟨t,ht.1.le,ht.2.le⟩
  by_cases hμν : μ=ν
  · subst ν
    exact integral_self_mul_derivative_eq_zero _ _
      (continuous_classicalHillTraceGradient q μ) (continuous_classicalHillTraceGradientPrime q μ)
      (hD μ) (classicalHillTraceGradient_boundary q μ).1
  · have hidentity := thirdOrder_periodic_lagrange_integral (extend q) Qdot
      (classicalHillTraceGradient q μ) (classicalHillTraceGradientPrime q μ) (classicalHillTraceGradientSecond q μ)
      (classicalHillTraceGradient q ν) (classicalHillTraceGradientPrime q ν) (classicalHillTraceGradientSecond q ν)
      μ ν (continuous_extend q)
      (continuous_classicalHillTraceGradient q μ) (continuous_classicalHillTraceGradientPrime q μ)
      (continuous_classicalHillTraceGradientSecond q μ)
      (continuous_classicalHillTraceGradient q ν) (continuous_classicalHillTraceGradientPrime q ν)
      (continuous_classicalHillTraceGradientSecond q ν) hq (hD μ)
      (fun t ht => hasDerivAt_classicalHillTraceGradientPrime q μ ⟨t,ht.1.le,ht.2.le⟩)
      (fun t ht => by
        have hd := hasDerivAt_classicalHillTraceGradientSecond q μ (Qdot t) ⟨t,ht.1.le,ht.2.le⟩ (hq t ht)
        simpa only [← extend_coe q ⟨t,ht.1.le,ht.2.le⟩] using hd)
      (hD ν) (fun t ht => hasDerivAt_classicalHillTraceGradientPrime q ν ⟨t,ht.1.le,ht.2.le⟩)
      (fun t ht => by
        have hd := hasDerivAt_classicalHillTraceGradientSecond q ν (Qdot t) ⟨t,ht.1.le,ht.2.le⟩ (hq t ht)
        simpa only [← extend_coe q ⟨t,ht.1.le,ht.2.le⟩] using hd)
      hperiod (classicalHillTraceGradient_boundary q μ).1 (classicalHillTraceGradient_boundary q μ).2
      (classicalHillTraceGradientSecond_boundary q μ hperiod)
      (classicalHillTraceGradient_boundary q ν).1 (classicalHillTraceGradient_boundary q ν).2
      (classicalHillTraceGradientSecond_boundary q ν hperiod)
    exact (mul_eq_zero.mp hidentity).resolve_left (sub_ne_zero.mpr hμν)

end NLS.KdV
