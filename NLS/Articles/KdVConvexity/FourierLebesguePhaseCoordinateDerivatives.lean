import NLS.Articles.KdVConvexity.FourierLebesguePhaseCompatibility
import NLS.KdV.HillRoughAbelianGardner
import NLS.ComplexAnalysis.ScalarDuhamel

/-! # Literal coordinate time derivatives of the actual physical phase evolution

Each coordinate solves its exact signed scalar ODE at every real time.
No finite support, native time derivative or PDE recovery is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity

theorem hasDerivAt_fourierLebesguePhaseEvolution_component
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (s : ℝ) (hs : -1/2≤s) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p)
    (σ : Bool) (n : ℕ+) (t : ℝ) :
    HasDerivAt (fun u : ℝ => hillRoughSignedAbelianComponent D.signed σ n
      (fourierLebesgueSourceInclusion s hs p hp h2p
        (D.fourierLebesguePhaseEvolution B s hs p hp h2p u q).val))
      (I*(signedPositiveFrequency
        (B.fourierLebesguePhysicalFrequency s hs p hp h2p (D.fourierLebesgueForward s hs p hp h2p q))
        (if σ then (n : ℤ) else -(n : ℤ)) : ℂ)*
          hillRoughSignedAbelianComponent D.signed σ n
            (fourierLebesgueSourceInclusion s hs p hp h2p
              (D.fourierLebesguePhaseEvolution B s hs p hp h2p t q).val)) t := by
  let j : ℤ := if σ then (n : ℤ) else -(n : ℤ)
  let ω : ℝ := signedPositiveFrequency
    (B.fourierLebesguePhysicalFrequency s hs p hp h2p (D.fourierLebesgueForward s hs p hp h2p q)) j
  let a := (D.signed (fourierLebesgueSourceInclusion s hs p hp h2p q.val)).val j
  let c : ℂ := I*(ω : ℂ)
  let f (u : ℝ) := hillRoughSignedAbelianComponent D.signed σ n
    (fourierLebesgueSourceInclusion s hs p hp h2p (D.fourierLebesguePhaseEvolution B s hs p hp h2p u q).val)
  have he (u : ℝ) : f u=Complex.exp (c*u)*a := by
    rw [show f u=(D.signed (fourierLebesgueSourceInclusion s hs p hp h2p
      (D.fourierLebesguePhaseEvolution B s hs p hp h2p u q).val)).val j from rfl,
      D.fourierLebesguePhaseEvolution_signed]
    change Complex.exp (((u*ω : ℝ) : ℂ)*I)*a=Complex.exp (c*u)*a
    congr 2
    dsimp only [c]
    push_cast
    ring
  have hd := (NLS.ComplexAnalysis.hasDerivAt_complex_exp_mul c t).mul_const a
  rw [←show f=(fun u : ℝ => Complex.exp (c*u)*a) from funext he] at hd
  have hv : Complex.exp (c*t)*c*a=I*(ω : ℂ)*f t := by
    rw [he t]
    dsimp only [c]
    ring
  rw [hv] at hd
  exact hd

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
