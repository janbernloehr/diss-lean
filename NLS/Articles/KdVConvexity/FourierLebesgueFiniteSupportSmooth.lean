import NLS.Articles.KdVConvexity.FourierLebesguePhaseEvolution
import NLS.KdV.HillRoughFiniteSupportSmooth

/-! # Finite native targets of the SAME inverse have smooth physical sources -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.Fourier
open scoped ENNReal ContDiff
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity
variable (D : GlobalRoughAbelianForwardData) (s : ℝ) (hs : -1/2≤s)
  (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]

theorem positive_finiteSupport_of_fourierLebesgue_target
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p)
    (hf : (Function.support z.val.val).Finite) :
    (Function.support (D.positive (fourierLebesgueSourceInclusion s hs p hp h2p
      ((D.fourierLebesgueEquiv s hs p hp h2p).symm z).val))).Finite := by
  let q := fourierLebesgueSourceInclusion s hs p hp h2p
    ((D.fourierLebesgueEquiv s hs p hp h2p).symm z).val
  have hr := fourierLebesgueSourceInclusion_real s hs p hp h2p
    ((D.fourierLebesgueEquiv s hs p hp h2p).symm z)
  have he := D.fourierLebesgueEquiv_symm_signed s hs p hp h2p z
  apply hf.subset
  intro j hj hz
  have hjpos : 0<j := by
    by_contra h
    exact hj (D.positive_zero q (D.real_mem_domain q hr) j (by omega))
  have hraw := congrArg (fun a => a.val j) he
  rw [D.signed_positive_real q hr j hjpos,fourierLebesgueTargetInclusion_apply,hz] at hraw
  have hden := (Weight.sobolev (-1/2)).complex_ne_zero j
  exact hj ((div_eq_zero_iff.mp hraw).resolve_right hden)

theorem exists_smooth_fourierLebesgue_inverse_of_finite_support
    (z : physicalRealMeanZeroWeightedExponent (Weight.sobolev (s+1/2)) p)
    (hf : (Function.support z.val.val).Finite) :
    ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧ ∀ n : ℤ,
      ((D.fourierLebesgueEquiv s hs p hp h2p).symm z).val.val n=periodOneCoefficient f n := by
  simpa only [fourierLebesgueSourceInclusion_apply] using
    D.exists_smooth_of_finite_positive_support _
      (fourierLebesgueSourceInclusion_real s hs p hp h2p ((D.fourierLebesgueEquiv s hs p hp h2p).symm z))
      (D.positive_finiteSupport_of_fourierLebesgue_target s hs p hp h2p z hf)

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
