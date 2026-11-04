import NLS.KdV.HillRegularAngleCompatibility
import NLS.ComplexAnalysis.RealAffineComplexPrimitive

/-! # Actual real-angle derivatives of the literal Abelian primitives

The original affine complex segment integral is the real interval integral
on the whole real angle line. The fundamental theorem therefore gives
its derivative at every real lift, including lifts outside [0,pi].
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.ZakharovShabat NLS.ComplexAnalysis
namespace NLS.KdV

theorem hasDerivAt_hillAbelianCosinePrimitive_real (q : RealPeriodOneHillPotential)
    (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) :
    HasDerivAt (fun x : ℝ => hillAbelianCosinePrimitive q.val q.property.1 q.property.2 n hn k (x : ℂ))
      (hillAbelianCosineDifferential q.val q.property.1 q.property.2 n hn k θ) θ := by
  let D := hillAbelianCosineDifferential q.val q.property.1 q.property.2 n hn k
  have hc : Continuous (fun x : ℝ => D (x : ℂ)) := continuous_iff_continuousAt.mpr (fun x =>
    (analyticAt_hillAbelianCosineDifferential_real q.val q.property.1 q.property.2 n hn k hk x).continuousAt.comp
      continuous_ofReal.continuousAt)
  have he : (fun x : ℝ => hillAbelianCosinePrimitive q.val q.property.1 q.property.2 n hn k (x : ℂ)) =
      (fun x => ∫ t in Real.pi..x,D (t : ℂ)) := by
    funext x
    exact real_affine_complex_integral_eq_intervalIntegral D Real.pi x
  rw [he]
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt

end NLS.KdV
