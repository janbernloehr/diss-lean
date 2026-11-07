import NLS.Articles.KdVKdV2Frequencies.AllTimeL2AiryBound
import NLS.Articles.KdVKdV2Frequencies.OriginalKdVPhysicalSolutions
import NLS.Articles.KdVKdV2Frequencies.TimeOrientation

/-! # Corollary 1.7: the actual KdV solution is one-smoothing relative to Airy

The solution class is the universal limit of EVERY smooth classical KdV
approximation in the ORIGINAL L2 norm. It has been proved nonvacuous and
unique using the literal physical PDE. The Airy group has coefficient
exp(i*(2*pi*j)^3*t), hence generator -partial_x^3 with the source's Fourier
convention. The H1 difference is realized by the literal Sobolev inclusion;
its positive bound works for ALL times and ALL data in ONE ORIGINAL-norm
open neighborhood of each initial datum. No bounded-on-whole-balls claim
or extra flow, coordinate, smoothing or frequency hypothesis is assumed. -/
noncomputable section
open Set Complex NLS.KdV
namespace NLS.Articles.KdVKdV2Frequencies

/-- The genuine universal classical-limit solution class in ORIGINAL L2_0. -/
def IsOriginalL2KdVSolution
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0))
    (u : ℝ → physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)) : Prop :=
  IsFourierLebesgueClassicalLimitSolution 0 (by norm_num) 2 (by norm_num) q u

/-- The full main assertion, with a LOCALLY UNIFORM positive C and EVERY
real time. The physical real H1 realization retains its inherited original
norm, and the same unique actual physical solution appears throughout. -/
theorem corollary_1_7 :
    (∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0),
      ∃! u : ℝ → physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0), IsOriginalL2KdVSolution q u) ∧
    ∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0),
      ∃ U : Set (physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0)),
        IsOpen U ∧ q∈U ∧ ∃ C : ℝ,0<C ∧
          ∀ p∈U,∀ u : ℝ → physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0),
            IsOriginalL2KdVSolution p u → ∀ t : ℝ,
              ∃ r : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 1),
                physicalRealMeanZeroSobolevInclusion (by norm_num : (0:ℝ)≤1) r=u t-originalAiryFlow 0 t p ∧
                  ‖r‖≤C*(1+|t|) := by
  obtain ⟨D⟩ := nonempty_globalRoughAbelianForwardData
  obtain ⟨V,G,hV,hcone,hG,hrec,B,_hB,_hclass,hsol⟩ := exists_actual_original_KdV_solution_family D
  have hphase := exists_actual_native_kdv_phase_gain D G V hV hcone hG hrec
  obtain ⟨R,hR,hbound⟩ := exists_original_l2_alltime_airy_remainder D G hphase
  constructor
  · intro q
    exact ⟨(fun t => originalKdVBirkhoffFlow D 0 (by norm_num) G t q),(hsol q).1,
      fun u hu => (hsol q).2 u hu⟩
  intro q
  obtain ⟨U,hU,hq,C,hC,hb⟩ := hbound q
  refine ⟨U,hU,hq,C,hC,?_⟩
  intro p hp u hu t
  have he := congrFun ((hsol p).2 u hu) t
  refine ⟨R t p,?_,hb p hp t⟩
  exact (hR t p).trans (congrArg (fun a => a-originalAiryFlow 0 t p) he.symm)

end NLS.Articles.KdVKdV2Frequencies
