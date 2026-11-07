import NLS.ComplexAnalysis.ShiftedSquareWeightedCircle

/-! Exact cubic shift of a weighted contour when its first and third
centered moments vanish. -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem circleIntegral_shifted_cube_of_odd_moments_zero
    (f g : ℂ → ℂ) (c a : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hf : ContinuousOn f (sphere c R)) (hg : ContinuousOn g (sphere c R))
    (h1 : (∮ z in C(c,R), f z*g z)=0)
    (h3 : (∮ z in C(c,R), (f z)^3*g z)=0) :
    (∮ z in C(c,R), (f z-a)^3*g z) =
      -3*a*(∮ z in C(c,R), (f z)^2*g z)-a^3*(∮ z in C(c,R), g z) := by
  have hi0 : CircleIntegrable g c R := hg.circleIntegrable hR
  have hi1 : CircleIntegrable (fun z => f z*g z) c R := (hf.mul hg).circleIntegrable hR
  have hi2 : CircleIntegrable (fun z => (f z)^2*g z) c R := ((hf.pow 2).mul hg).circleIntegrable hR
  have hi3 : CircleIntegrable (fun z => (f z)^3*g z) c R := ((hf.pow 3).mul hg).circleIntegrable hR
  have hic0 : CircleIntegrable (fun z => (-a^3)*g z) c R := hi0.const_mul (-a^3)
  have hic1 : CircleIntegrable (fun z => (3*a^2)*(f z*g z)) c R := hi1.const_mul (3*a^2)
  have hic2 : CircleIntegrable (fun z => (-3*a)*((f z)^2*g z)) c R := hi2.const_mul (-3*a)
  have h32 := circleIntegral.integral_add hi3 hic2
  have h321 := circleIntegral.integral_add (hi3.add hic2) hic1
  have hall := circleIntegral.integral_add ((hi3.add hic2).add hic1) hic0
  dsimp only [Pi.add_apply] at h32 h321 hall
  calc
    _ = ∮ z in C(c,R), (((f z)^3*g z+(-3*a)*((f z)^2*g z))+
        (3*a^2)*(f z*g z))+(-a^3)*g z := by
      apply circleIntegral.integral_congr hR
      intro z _
      dsimp only
      ring
    _ = _ := by
      rw [hall,h321,h32,
        circleIntegral.integral_const_mul,circleIntegral.integral_const_mul,
        circleIntegral.integral_const_mul,h1,h3]
      ring

end NLS.ComplexAnalysis
