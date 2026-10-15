import NLS.ZakharovShabat.SourceSection23Actions
import NLS.ZakharovShabat.SourceTheorem23_4
import NLS.ZakharovShabat.SourceCorollary23_5

/-! # Original weighted and fractional Sobolev estimates

Every weighted neighborhood contains all normalized real sources. Its
actual decoded sources stay inside the retained original complex domain.
-/
noncomputable section
open Set NLS
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceSection20Data
variable {W₀ W V Wa B U : Set (CoeffPair 2)}
  {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
  (Q : SourceSection20Data D A B U)
include Q

/-- Theorem 23.4 with original indexed actions, original coordinates, and one
weighted complex neighborhood mapped into the retained original source domain. -/
theorem section23_weighted_neighborhood (w : SpectralWeight) (hw : w.HasLinearFactor) :
    ∃ T : Set (CoeffPair 2), IsOpen T ∧ realTypeSourceLocus 2 ⊆ T ∧
      (∀ a ∈ T, normalizedWeightedSource w a ∈ U) ∧
      (∀ a ∈ T,
        Summable (fun n : ℤ => (w (2*n))^2*
          ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖) ∧
        (∑' n : ℤ, (w (2*n))^2*
          ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖) ≤
            (2048:ℝ)^2*(w.realExtension (16*‖a‖^2))^2*‖a‖^2) ∧
      ∀ a : realTypeSourceSubmodule 2,
        ‖D.complex.m1Coordinates w hw a‖ ≤ 2048*w.realExtension (16*‖a.val‖^2)*‖a.val‖ := by
  obtain ⟨T,hT,hr,hb⟩ := exists_sourceM1Action_neighborhood w hw
  let R := T ∩ (normalizedWeightedSource w) ⁻¹' U
  have hR : IsOpen R := hT.inter (Q.source_open.preimage (continuous_normalizedWeightedSource w))
  have hrR : realTypeSourceLocus 2 ⊆ R := fun a ha =>
    ⟨hr ha,Q.real_subset (normalizedWeightedSource_realType w a ha)⟩
  refine ⟨R,hR,hrR,fun _ ha => ha.2,?_,D.complex.m1Coordinates_norm_le w hw⟩
  intro a ha
  have he (n : ℤ) := D.indexed_action_eq_complex (normalizedWeightedSource w a) (Q.original_subset ha.2) n
  simp_rw [he]
  refine ⟨(hb a ha.1).1,?_⟩
  exact (hb a ha.1).2.trans (by gcongr; norm_num)

/-- Corollary 23.5 at every real order at least one, with the same positive
constant in the action and coordinate bounds and the literal powers 4r and 2r. -/
theorem section23_realSobolev_neighborhood (r : ℝ) (hr : 1 ≤ r) :
    ∃ T : Set (CoeffPair 2), IsOpen T ∧ realTypeSourceLocus 2 ⊆ T ∧
      (∀ a ∈ T, sourceRealSobolevInclusion r (zero_le_one.trans hr) a ∈ U) ∧
      (∀ a ∈ T,
        Summable (fun n : ℤ => (1+|((2*n:ℤ):ℝ)*Real.pi|)^(2*r)*
          ‖sourceIndexedAction (by simp) (by norm_num) n
            (sourceRealSobolevInclusion r (zero_le_one.trans hr) a)‖) ∧
        (∑' n : ℤ, (1+|((2*n:ℤ):ℝ)*Real.pi|)^(2*r)*
          ‖sourceIndexedAction (by simp) (by norm_num) n
            (sourceRealSobolevInclusion r (zero_le_one.trans hr) a)‖) ≤
          (realSobolevEstimateConstant r)^2*(1+‖a‖)^(4*r)*‖a‖^2) ∧
      ∀ a : realTypeSourceSubmodule 2,
        ‖D.complex.realSobolevCoordinates r hr a‖ ≤
          realSobolevEstimateConstant r*(1+‖a.val‖)^(2*r)*‖a.val‖ := by
  obtain ⟨T,hT,hreal,hbound⟩ := exists_sourceRealSobolev_action_neighborhood r hr
  let w := SpectralWeight.piSobolev r (zero_le_one.trans hr)
  let R := T ∩ (sourceRealSobolevInclusion r (zero_le_one.trans hr)) ⁻¹' U
  have hR : IsOpen R := hT.inter (Q.source_open.preimage (continuous_normalizedWeightedSource w))
  have hrR : realTypeSourceLocus 2 ⊆ R := fun a ha =>
    ⟨hreal ha,Q.real_subset (normalizedWeightedSource_realType w a ha)⟩
  refine ⟨R,hR,hrR,fun _ ha => ha.2,?_,D.complex.realSobolevCoordinates_norm_le r hr⟩
  intro a ha
  have he (n : ℤ) := D.indexed_action_eq_complex
    (sourceRealSobolevInclusion r (zero_le_one.trans hr) a) (Q.original_subset ha.2) n
  simp_rw [he]
  exact hbound a ha.1

end NLS.ZakharovShabat.SourceSection20Data
