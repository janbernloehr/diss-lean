import NLS.KdV.HillHalfSandwichSmall
import NLS.Articles.KdVPseudomeasures.SpectralResolvent

/-! The actual Appendix C.4 normalized periodic perturbation S_lambda,
with the ENTIRE original complex H^t potential and source L2 normalization. -/
noncomputable section
open Set Metric
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- The source normalized perturbation on ALL physical periodic L2 inputs,
from the original distribution with its exact original Sobolev norm. -/
def sourcePeriodicNormalizedPerturbation (r : ℝ)
    (q : FourierLebesgueSpace (2:ℝ) (-r) 2) (z : ℂ) : CircleL2 →L[ℂ] CircleL2 :=
  hillPhysicalHalfSandwich r (sobolevCoefficients (-r) 2 q) z

/-- Its actual physical Fourier row retains EVERY ORIGINAL potential mode
and ALL ORIGINAL input modes, with the literal source half-denominators. -/
theorem sourcePeriodicNormalizedPerturbation_coefficient (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : FourierLebesgueSpace (2:ℝ) (-r) 2) (n : ℕ+) (hlog : 1 < Real.log (n:ℝ)) (z : ℂ)
    (hz : z ∈ sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)) (F : CircleL2) (l : ℤ) :
    fourierCoeff (sourcePeriodicNormalizedPerturbation r q z F) l = ∑' m : ℤ,
      q.val (NLS.Fourier.SmoothPeriodicTest.mode (-(l-m)))*
        hillHalfDenominatorRaw z l*hillHalfDenominatorRaw z m*fourierCoeff F m := by
  have hz' : z ∈ sphere (freeHillValue (n:ℕ):ℂ) (n:ℝ) := by
    rwa [freeHillValue_natCast_complex]
  have h := hillPhysicalHalfSandwich_coefficient r hr hr1 (sobolevCoefficients (-r) 2 q)
    (n:ℕ) n.property hlog z hz' F l
  simpa only [sourcePeriodicNormalizedPerturbation,sobolevCoefficients_apply] using h

/-- The source normalized perturbation has the sharp squared rough-potential
bound in the ORIGINAL Sobolev norm, uniformly on the ENTIRE literal circle. -/
theorem norm_sq_sourcePeriodicNormalizedPerturbation_le (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (q : FourierLebesgueSpace (2:ℝ) (-r) 2) (n : ℕ+) (hlog : 1 < Real.log (n:ℝ)) (z : ℂ)
    (hz : z ∈ sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ)) :
    ‖sourcePeriodicNormalizedPerturbation r q z‖^2 ≤
      (128*(8*Real.exp 1+2)*Real.log (n:ℝ)*(n:ℝ)^(2*r-2))*‖q‖^2 := by
  have hz' : z ∈ sphere (freeHillValue (n:ℕ):ℂ) (n:ℝ) := by
    rwa [freeHillValue_natCast_complex]
  have h := norm_sq_hillPhysicalHalfSandwich_le r hr hr1 (sobolevCoefficients (-r) 2 q)
    (n:ℕ) n.property hlog z hz'
  simpa only [sourcePeriodicNormalizedPerturbation,LinearIsometryEquiv.norm_map] using h

/-- ONE original Sobolev norm-ball threshold precedes EVERY complex source,
ALL later original positive indices and ALL points on each literal source
circle, with actual physical L2 perturbation norm at most ONE HALF. -/
theorem exists_uniform_sourcePeriodicNormalizedPerturbation_small (r : ℝ) (hr : 0 ≤ r)
    (hr1 : r < 1) (R : ℝ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ q : FourierLebesgueSpace (2:ℝ) (-r) 2, ‖q‖ ≤ R →
      ∀ n : ℕ+, N ≤ (n:ℕ) → ∀ z ∈ sphere (((Real.pi:ℂ)*(n:ℕ))^2) (n:ℝ),
        ‖sourcePeriodicNormalizedPerturbation r q z‖ ≤ 1/2 := by
  obtain ⟨N,hN,hsmall⟩ := exists_uniform_hillPhysicalHalfSandwich_small r hr hr1 R
  refine ⟨N,hN,?_⟩
  intro q hq n hn z hz
  have hz' : z ∈ sphere (freeHillValue (n:ℕ):ℂ) (n:ℝ) := by
    rwa [freeHillValue_natCast_complex]
  exact (hsmall (n:ℕ) hn).2 (sobolevCoefficients (-r) 2 q)
    (by simpa only [LinearIsometryEquiv.norm_map] using hq) z hz'

end NLS.Articles.KdVPseudomeasures
