import Mathlib.MeasureTheory.Integral.CircleIntegral

/-! # Continuous bilinear maps and two contour integrals

A continuous linear map commutes with an integrable circle integral.
Applying this in each argument of a continuous bilinear map expresses
the pairing of two contour integrals as an iterated contour integral.
This will transport the discriminant's spectral commutation identity
to the action variables.
-/

noncomputable section
open Complex
namespace NLS.ComplexAnalysis
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

theorem map_circleIntegral (L : E →L[ℂ] F) {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) :
    L (∮ z in C(c,R), f z) = ∮ z in C(c,R), L (f z) := by
  simpa only [circleIntegral,map_smul] using (L.intervalIntegral_comp_comm hf.out).symm

theorem bilinear_circleIntegral (B : E →L[ℂ] F →L[ℂ] G)
    {f : ℂ → E} {g : ℂ → F} {c d : ℂ} {R S : ℝ}
    (hf : CircleIntegrable f c R) (hg : CircleIntegrable g d S) :
    B (∮ z in C(c,R), f z) (∮ w in C(d,S), g w) =
      ∮ z in C(c,R), ∮ w in C(d,S), B (f z) (g w) := by
  have hleft := map_circleIntegral (B.flip (∮ w in C(d,S), g w)) hf
  change B (∮ z in C(c,R), f z) (∮ w in C(d,S), g w) =
    ∮ z in C(c,R), B (f z) (∮ w in C(d,S), g w) at hleft
  rw [hleft]
  congr 1
  funext z
  exact map_circleIntegral (B (f z)) hg

end NLS.ComplexAnalysis
