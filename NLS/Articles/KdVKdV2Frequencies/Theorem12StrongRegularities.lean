import NLS.Articles.KdVKdV2Frequencies.Theorem12StrongEndpoint
import NLS.SequenceSpaces.AnalyticPacketPullback

/-! The ENTIRE s>=-1/2 unweighted-target range of Theorem1.2(i).
The source is the ORIGINAL raw ell(2s+1,1) action norm, its entire
positive cone lies in each complex domain, and every r>1 target has
the SAME raw frequency coefficients as the physically calibrated map. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV
open NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

theorem strong_regularity_target_pullback (α : ℝ) (hα : 0≤α)
    {r : ℝ≥0∞} [Fact (1 ≤ r)] (ω : Coeff 1 → ℤ → ℂ)
    (V : Set (Coeff 1)) (F : Coeff 1 → Coeff r)
    (hV : IsOpen V) (hcone : Coeff.nonnegativeLocus 1⊆V) (hF : AnalyticOnNhd ℂ F V)
    (hzero : ∀ a∈V, ∀ j : ℤ, j≤0 → F a j=0)
    (hrec : ∀ a∈Coeff.nonnegativeLocus 1, ∀ j : ℤ, F a j=ω a j) :
    ∃ U : Set (WeightedCoeff (Weight.sobolev α) 1),
      ∃ G : WeightedCoeff (Weight.sobolev α) 1 → Coeff r,
        IsOpen U ∧ WeightedCoeff.positiveActionLocus (Weight.sobolev α) 1⊆U ∧
        AnalyticOnNhd ℂ G U ∧ (∀ a∈U, ∀ j : ℤ, j≤0 → G a j=0) ∧
        ∀ a∈WeightedCoeff.positiveActionLocus (Weight.sobolev α) 1, ∀ j : ℤ,
          G a j=ω (WeightedCoeff.nonnegativeSobolevToCoeffCLM α hα a) j :=
  exists_analytic_cone_pullback (WeightedCoeff.nonnegativeSobolevToCoeffCLM α hα)
    (WeightedCoeff.positiveActionLocus (Weight.sobolev α) 1) (Coeff.nonnegativeLocus 1) V
    (fun (b : Coeff r) (j : ℤ) => b j) ω F
    (fun a ha => WeightedCoeff.nonnegativeSobolevToCoeffCLM_nonnegative α hα a ha.1)
    hV hcone hF hzero hrec

/-- ONE actual raw frequency map, with physical native recovery, admits
genuine Banach analytic unweighted ellr extensions near the ENTIRE
original ell(2s+1,1) positive action cone, for EVERY s>=-1/2 and EVERY
r>1. Each domain precedes ALL action points and ALL frequency indices.
The intermediate negative orders, asymptotics and compactness remain separate. -/
theorem GlobalRoughAbelianForwardData.theorem_1_2_i_strong_regularities
    (D : GlobalRoughAbelianForwardData) :
    ∃ ω : Coeff 1 → ℤ → ℂ,
      (∀ a : Coeff 1, ∀ j : ℤ, j≤0 → ω a j=0) ∧
      (∀ a∈Coeff.nonnegativeLocus 1, ∀ j : ℤ, (ω a j).im=0) ∧
      (∀ q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev ((1 : ℕ) : ℝ)),
        D.nativeRawKdVActions q∈Coeff.nonnegativeLocus 1 ∧ ∀ n : ℕ+,
          ω (D.nativeRawKdVActions q) (n : ℤ)=
            (D.nativeSourceHierarchyFrequency 1 3 (by norm_num) q n : ℂ)-(2*(n : ℂ)*Real.pi)^3) ∧
      ∀ s : ℝ, ∀ hs : -1/2≤s, ∀ r : ℝ≥0∞, ∀ hr : 1<r,
        letI : Fact (1 ≤ r) := ⟨hr.le⟩;
        ∃ U : Set (WeightedCoeff (Weight.sobolev (2*s+1)) 1),
          ∃ F : WeightedCoeff (Weight.sobolev (2*s+1)) 1 → Coeff r,
            IsOpen U ∧ WeightedCoeff.positiveActionLocus (Weight.sobolev (2*s+1)) 1⊆U ∧
            AnalyticOnNhd ℂ F U ∧ (∀ a∈U, ∀ j : ℤ, j≤0 → F a j=0) ∧
            ∀ a∈WeightedCoeff.positiveActionLocus (Weight.sobolev (2*s+1)) 1, ∀ j : ℤ,
              F a j=ω (WeightedCoeff.nonnegativeSobolevToCoeffCLM (2*s+1) (by linarith) a) j := by
  obtain ⟨ω,hzero,hreal,hnative,hall⟩ := D.theorem_1_2_i_strong_endpoint
  refine ⟨ω,hzero,hreal,hnative,?_⟩
  intro s hs r hr
  let : Fact (1 ≤ r) := ⟨hr.le⟩
  obtain ⟨V,F,hV,hcone,hF,hFzero,hrec⟩ := hall r hr
  exact strong_regularity_target_pullback (2*s+1) (by linarith) ω V F hV hcone hF hFzero hrec

end NLS.Articles.KdVKdV2Frequencies
