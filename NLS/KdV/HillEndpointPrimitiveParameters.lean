import NLS.KdV.HillAbelianCosinePrimitivePeriods
import NLS.KdV.HillPhysicalGermDerivativeUniqueness

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The actual fixed-endpoint Abelian primitive has zero parameter cotangent:
its physical value is the fixed normalized period or zero. -/
theorem hillAbelianPrimitive_endpoint_parameter_fderiv_eq_zero
    (q : RealPeriodOneHillPotential) (n k : ℕ) (hn : 1≤n) (hk : 1≤k)
    (e : ℂ) (he : e=0 ∨ e=(Real.pi : ℂ))
    (F : Coeff 2 → ℂ) (hF : AnalyticAt ℂ F (SpectralWeight.one.toCoeff q.val))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (SpectralWeight.one.toCoeff p.val)=hillAbelianCosinePrimitive p.val p.property.1 p.property.2 n hn k e)
    (h : WeightedCoeff SpectralWeight.one.toWeight 2)
    (heven : SpectralWeight.one.toCoeff h∈Coeff.paritySubspace 0) :
    (fderiv ℂ F (SpectralWeight.one.toCoeff q.val)) (SpectralWeight.one.toCoeff h)=0 := by
  let c : ℂ := if e=0 then -(Real.pi : ℂ)*(if k=n then 1 else 0) else 0
  have heq : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 q,
      F (SpectralWeight.one.toCoeff p.val)=(fun _ : Coeff 2 => c) (SpectralWeight.one.toCoeff p.val) := by
    filter_upwards [hmatch] with p hp
    rw [hp]
    rcases he with he | he
    · rw [he,hillAbelianCosinePrimitive_zero p.val p.property.1 p.property.2 n hn k hk]
      simp only [c,he,if_true]
    · rw [he,hillAbelianCosinePrimitive_pi]
      simp only [c,he,ofReal_eq_zero,Real.pi_ne_zero,if_false]
  have hd := hillPhysicalCoefficientGerm_fderiv_eq_of_eventuallyEq q.val q.property.1 q.property.2
    F (fun _ => c) hF analyticAt_const heq h heven
  simpa only [fderiv_const_apply,zero_apply] using hd

end NLS.KdV
