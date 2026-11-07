import NLS.Articles.KdVConvexity.FourierLebesgueClassicalApproximation
import NLS.SequenceSpaces.PhysicalWeightedRawSequence

/-! # Actual smooth H4 potentials are dense in every original article space

The previously constructed finite-gap approximations supply smooth
physical functions. Their H4 representatives preserve every original
signed coefficient and converge in the native Fourier-Lebesgue norm.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV NLS.Fourier
open scoped ENNReal ContDiff
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity

theorem exists_smooth_H4_of_smooth_coefficients
    (s : ℝ) (h4s : s≤4) (p : ℝ≥0∞) (h2p : 2≤p) [Fact (1≤p)]
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p)
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hp : Function.Periodic f 1)
    (hc : ∀ n : ℤ, q.val.val n=periodOneCoefficient f n) :
    ∃ a : physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2,
      IsSmoothPeriodOnePotential a ∧ physicalSobolevExponentInclusion h4s h2p a=q := by
  have h4 : Memℓp (fun n => (Weight.sobolev 4 n : ℂ)*q.val.val n) 2 := by
    simp_rw [hc]
    exact (memlp_periodOneCoefficient_sobolev_one 4 (by norm_num) f hf hp).of_exponent_ge (by norm_num)
  let a := physicalWeightedRawSequence (Weight.sobolev 4) 2 q.val.val h4 q.property.1 q.property.2
  have ha (n : ℤ) : a.val.val n=q.val.val n :=
    physicalWeightedRawSequence_apply (Weight.sobolev 4) 2 q.val.val h4 q.property.1 q.property.2 n
  refine ⟨a,(isSmoothPeriodOnePotential_iff_exists_smooth a).mpr
    ⟨f,hf,hp,fun n => (ha n).trans (hc n)⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext n
  exact (physicalSobolevExponentInclusion_apply h4s h2p a n).trans (ha n)

theorem exists_smooth_H4_approximation
    (D : GlobalRoughAbelianForwardData)
    (s : ℝ) (hs : -1/2≤s) (h4s : s≤4) (p : ℝ≥0∞) (hp : p≠⊤) (h2p : 2≤p) [Fact (1≤p)]
    (q : physicalRealMeanZeroWeightedExponent (Weight.sobolev s) p) :
    ∃ a : ℕ → physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2,
      (∀ N, IsSmoothPeriodOnePotential (a N)) ∧
      Tendsto (fun N => physicalSobolevExponentInclusion h4s h2p (a N)) atTop (𝓝 q) := by
  have hex (N : ℕ) : ∃ a : physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2,
      IsSmoothPeriodOnePotential a ∧ physicalSobolevExponentInclusion h4s h2p a=
        D.fourierLebesgueFiniteGapApproximation s hs p hp h2p q N := by
    obtain ⟨f,hf,hper,hc⟩ := D.fourierLebesgueFiniteGapApproximation_smooth s hs p hp h2p q N
    exact exists_smooth_H4_of_smooth_coefficients s h4s p h2p _ f hf hper hc
  choose a ha he using hex
  refine ⟨a,ha,?_⟩
  simp_rw [he]
  exact D.tendsto_fourierLebesgueFiniteGapApproximation s hs p hp h2p q

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
