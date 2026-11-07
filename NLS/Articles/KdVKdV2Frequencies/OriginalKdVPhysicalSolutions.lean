import NLS.Articles.KdVKdV2Frequencies.OriginalPhysicalKdVFlowMatching
import NLS.Articles.KdVConvexity.FourierLebesgueClassicalLimitUniqueness
import NLS.Articles.KdVConvexity.WeakPhysicalClassicalLimit

/-! Actual PDE recovery and universal classical-approximation uniqueness
for the SAME retained original-norm KdV evolution. The calibrated family
is constructed, so no physical solution or frequency-extension hypothesis
is left as an essential unproved dependency. All-time one-smoothing bounds
remain a separate obligation for Corollary 1.7. -/
noncomputable section
open Set Complex Filter Topology NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal ContDiff
namespace NLS.Articles.KdVKdV2Frequencies
open GlobalRoughAbelianForwardData

theorem original_flow_is_classicalKdV
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (G : ℕ+ → Coeff 1 → ℂ)
    (hB : ∀ n a,B.frequency n a=G n (baseActionNormalization a)+(2*(n:ℂ)*Real.pi)^3)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 4)) :
    IsPeriodOneClassicalKdVCurve (fun t => originalKdVBirkhoffFlow D 4 (by norm_num) G t q) := by
  simpa only [original_flow_eq_physical_evolution D B G hB 4 (by norm_num)] using
    D.fourierLebesguePhaseEvolution_isClassicalKdV B q

theorem original_flow_is_classicalLimitSolution
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (G : ℕ+ → Coeff 1 → ℂ)
    (hB : ∀ n a,B.frequency n a=G n (baseActionNormalization a)+(2*(n:ℂ)*Real.pi)^3)
    (s : ℝ) (hs : -1/2≤s) (h4s : s≤4)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s)) :
    IsFourierLebesgueClassicalLimitSolution s h4s 2 (by norm_num) q
      (fun t => originalKdVBirkhoffFlow D s (by linarith) G t q) := by
  simpa only [original_flow_eq_physical_evolution D B G hB s hs] using
    D.fourierLebesguePhaseEvolution_isClassicalLimitSolution B s hs h4s 2 (by simp) (by norm_num) q

theorem original_classicalLimitSolution_unique
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (G : ℕ+ → Coeff 1 → ℂ)
    (hB : ∀ n a,B.frequency n a=G n (baseActionNormalization a)+(2*(n:ℂ)*Real.pi)^3)
    (s : ℝ) (hs : -1/2≤s) (h4s : s≤4)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s))
    (γ : ℝ → physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s))
    (hγ : IsFourierLebesgueClassicalLimitSolution s h4s 2 (by norm_num) q γ) :
    γ=(fun t => originalKdVBirkhoffFlow D s (by linarith) G t q) := by
  simpa only [original_flow_eq_physical_evolution D B G hB s hs] using!
    D.classicalLimitSolution_eq_fourierLebesguePhaseEvolution B s hs h4s 2 (by simp) (by norm_num) q γ hγ

theorem original_arbitrary_classical_approximation
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (G : ℕ+ → Coeff 1 → ℂ)
    (hB : ∀ n a,B.frequency n a=G n (baseActionNormalization a)+(2*(n:ℂ)*Real.pi)^3)
    (s : ℝ) (hs : -1/2≤s) (h4s : s≤4)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev s))
    (a : ℕ → physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 4))
    (ha : Tendsto (fun N => physicalSobolevExponentInclusion h4s (by norm_num : (2:ℝ≥0∞)≤2) (a N)) atTop (𝓝 q))
    (U : ℕ → ℝ → physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 4))
    (hU : ∀ N, IsPeriodOneClassicalKdVCurve (U N)) (hzero : ∀ N,U N 0=a N)
    (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn (fun N t => physicalSobolevExponentInclusion h4s (by norm_num : (2:ℝ≥0∞)≤2) (U N t))
      (fun t => originalKdVBirkhoffFlow D s (by linarith) G t q) atTop K := by
  simpa only [original_flow_eq_physical_evolution D B G hB s hs] using
    D.tendstoUniformlyOn_arbitrary_classicalKdV_approximation B s hs h4s 2 (by simp) (by norm_num) q a ha U hU hzero K hK

theorem original_smooth_flow_literalKdV
    (D : GlobalRoughAbelianForwardData) (B : BasePhysicalFrequencyExtension)
    (G : ℕ+ → Coeff 1 → ℂ)
    (hB : ∀ n a,B.frequency n a=G n (baseActionNormalization a)+(2*(n:ℂ)*Real.pi)^3)
    (q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 4))
    (hq : IsSmoothPeriodOnePotential q) (t : ℝ) :
    ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ Function.Periodic f 1 ∧
      (∀ k : ℤ,(originalKdVBirkhoffFlow D 4 (by norm_num) G t q).val.val k=NLS.Fourier.periodOneCoefficient f k) ∧
      ∃ v : C(AddCircle (2:ℝ),ℂ),
        HasDerivAt (periodOneClassicalKdVPhysical (fun r => originalKdVBirkhoffFlow D 4 (by norm_num) G r q)) v t ∧
        (∀ x : ℝ,periodOneClassicalKdVPhysical (fun r => originalKdVBirkhoffFlow D 4 (by norm_num) G r q)
          t (x : AddCircle (2:ℝ))=f x) ∧ ∀ x : ℝ,v (x : AddCircle (2:ℝ))=kdvRHS f x := by
  simpa only [original_flow_eq_physical_evolution D B G hB 4 (by norm_num)] using
    D.smooth_fourierLebesguePhaseEvolution_literalKdV B q hq t

/-- The calibrated family exists and the SAME retained L2 evolution is
an actual, unique universal classical-limit KdV solution at EVERY datum.
The H4 trajectories obey the strong PDE, whose smooth representatives
have exactly -u_xxx+6*u*u_x as their physical velocity. -/
theorem exists_actual_original_KdV_solution_family (D : GlobalRoughAbelianForwardData) :
    ∃ V : Set (Coeff 1),∃ G : ℕ+ → Coeff 1 → ℂ,
      IsOpen V ∧ Coeff.nonnegativeLocus 1⊆V ∧ (∀ n,AnalyticOnNhd ℂ (G n) V) ∧
      (∀ (P : PhysicalFrequencyPairChart D) (z : Coeff 2 × Coeff 2),
        z∈P.domain → z∈Coeff.realPairLocus 2 → ∀ n,G n (quadraticActionsExponent (q := 1) z)=P.correction n z) ∧
      ∃ B : BasePhysicalFrequencyExtension,
        (∀ n a,B.frequency n a=G n (baseActionNormalization a)+(2*(n:ℂ)*Real.pi)^3) ∧
        (∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 4),
          IsPeriodOneClassicalKdVCurve (fun t => originalKdVBirkhoffFlow D 4 (by norm_num) G t q)) ∧
        ∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0),
          IsFourierLebesgueClassicalLimitSolution 0 (by norm_num) 2 (by norm_num) q
            (fun t => originalKdVBirkhoffFlow D 0 (by norm_num) G t q) ∧
          ∀ γ : ℝ → physicalRealMeanZeroWeightedSubmodule (Weight.sobolev 0),
            IsFourierLebesgueClassicalLimitSolution 0 (by norm_num) 2 (by norm_num) q γ →
              γ=(fun t => originalKdVBirkhoffFlow D 0 (by norm_num) G t q) := by
  obtain ⟨V,G,hV,hcone,hG,hrec⟩ := exists_global_physical_frequency_action_corrections D
  obtain ⟨B,hB⟩ := exists_calibrated_base_frequency D V G hV hcone hG hrec
  refine ⟨V,G,hV,hcone,hG,hrec,B,hB,?_,?_⟩
  · exact original_flow_is_classicalKdV D B G hB
  intro q
  exact ⟨original_flow_is_classicalLimitSolution D B G hB 0 (by norm_num) (by norm_num) q,
    fun γ hγ => original_classicalLimitSolution_unique D B G hB 0 (by norm_num) (by norm_num) q γ hγ⟩

end NLS.Articles.KdVKdV2Frequencies
