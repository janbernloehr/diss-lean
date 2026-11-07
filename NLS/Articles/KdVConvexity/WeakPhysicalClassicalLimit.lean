import NLS.Articles.KdVConvexity.ClassicalKdVUniqueness
import NLS.Articles.KdVConvexity.WeakPhysicalPhaseEvolution
import NLS.KdV.PeriodOneSmoothPotential

/-! # Identification with the actual Hminus1 classical-limit evolution

Weak convergence of arbitrary smooth initial sequences suffices. Their
actual classical KdV curves converge in the fixed original weak Hilbert
chart, uniformly on compact time sets, to the same weak phase evolution.
-/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
open NLS.Articles.KdVConvexity

theorem classicalKdV_weak_normalization_eq_phase
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (u : ℝ → physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2)
    (hu : IsPeriodOneClassicalKdVCurve u) (t : ℝ) :
    fourierLebesgueSourceNormalization 4 (by norm_num) 2 (by simp) (by norm_num) (u t)=
      D.weakPhysicalPhaseEvolution B t
        (fourierLebesgueSourceNormalization 4 (by norm_num) 2 (by simp) (by norm_num) (u 0)) := by
  rw [D.classicalKdV_eq_fourierLebesguePhaseEvolution B u hu t]
  exact D.fourierLebesguePhaseEvolution_weak_commuting B 4 (by norm_num) 2 (by simp) (by norm_num) t (u 0)

theorem tendstoUniformlyOn_arbitrary_classicalKdV_weak_approximation
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (q : physicalRealDeletedSubmodule)
    (a : ℕ → physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2)
    (ha : Tendsto (fun N => fourierLebesgueSourceNormalization 4 (by norm_num) 2 (by simp) (by norm_num) (a N))
      atTop (𝓝 q))
    (U : ℕ → ℝ → physicalRealMeanZeroWeightedExponent (Weight.sobolev 4) 2)
    (hU : ∀ N, IsPeriodOneClassicalKdVCurve (U N)) (hzero : ∀ N, U N 0=a N)
    (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun N t => fourierLebesgueSourceNormalization 4 (by norm_num) 2 (by simp) (by norm_num) (U N t))
      (fun t => D.weakPhysicalPhaseEvolution B t q) atTop K := by
  have he (N : ℕ) (t : ℝ) : fourierLebesgueSourceNormalization 4 (by norm_num) 2 (by simp) (by norm_num) (U N t)=
      D.weakPhysicalPhaseEvolution B t
        (fourierLebesgueSourceNormalization 4 (by norm_num) 2 (by simp) (by norm_num) (a N)) := by
    rw [D.classicalKdV_weak_normalization_eq_phase B (U N) (hU N) t,hzero N]
  simp_rw [he]
  exact NLS.Dynamics.tendstoUniformlyOn_conjugatedEvolution D.realWeakHomeomorph
    B.weakPhysicalPhaseFlow B.continuous_weakPhysicalPhaseFlow ha K hK

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
