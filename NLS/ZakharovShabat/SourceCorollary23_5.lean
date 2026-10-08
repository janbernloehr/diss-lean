import NLS.ZakharovShabat.SourceRealSobolevCoordinates
import NLS.ZakharovShabat.SourceM1ActionNeighborhood
import NLS.ZakharovShabat.SourceBirkhoffM1Estimate
import NLS.SequenceSpaces.SobolevWeightInterpolationBound

/-! # Corollary 23.5: polynomial estimates for every real Sobolev order s ≥ 1 -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- One explicit constant works for both conclusions at order s. -/
def realSobolevEstimateConstant (r : ℝ) : ℝ := 2048*(1+17*Real.pi)^r

theorem realSobolevEstimateConstant_pos (r : ℝ) : 0 < realSobolevEstimateConstant r := by
  unfold realSobolevEstimateConstant
  positivity

/-- The complex action estimate has the printed real exponent 4s and includes
absolute summability on a neighborhood of the whole real source space. -/
theorem exists_sourceRealSobolev_action_neighborhood (r : ℝ) (hr : 1 ≤ r) :
    ∃ V : Set (CoeffPair 2), IsOpen V ∧ realTypeSourceLocus 2 ⊆ V ∧ ∀ a ∈ V,
      Summable (sourceRealSobolevActionTerm r (zero_le_one.trans hr) a) ∧
      (∑' n : ℤ, sourceRealSobolevActionTerm r (zero_le_one.trans hr) a n) ≤
        (realSobolevEstimateConstant r)^2*(1+‖a‖)^(4*r)*‖a‖^2 := by
  let w := SpectralWeight.piSobolev r (zero_le_one.trans hr)
  obtain ⟨V,hV,hreal,hbound⟩ := exists_sourceM1Action_neighborhood w
    (SpectralWeight.hasLinearFactor_piSobolev r hr)
  refine ⟨V,hV,hreal,?_⟩
  intro a ha
  have hs : Summable (sourceRealSobolevActionTerm r (zero_le_one.trans hr) a) := by
    exact (hbound a ha).1.congr (fun n =>
      (sourceRealSobolevActionTerm_eq r (zero_le_one.trans hr) a n).symm)
  have hweight := SpectralWeight.piSobolev_realExtension_sixteen_sq_le r
    (zero_le_one.trans hr) ‖a‖ (norm_nonneg a)
  refine ⟨hs,?_⟩
  calc
    _ ≤ (2:ℝ)^21*(w.realExtension (16*‖a‖^2))^2*‖a‖^2 := by
      simpa only [sourceRealSobolevActionTerm_eq] using (hbound a ha).2
    _ ≤ (2048:ℝ)^2*(w.realExtension (16*‖a‖^2))^2*‖a‖^2 := by gcongr; norm_num
    _ ≤ (2048:ℝ)^2*(((1+17*Real.pi)^r)^2*(1+‖a‖)^(4*r))*‖a‖^2 := by gcongr
    _ = _ := by unfold realSobolevEstimateConstant; ring

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)}
  {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- The real Birkhoff estimate at order s has the printed exponent 2s. -/
theorem realSobolevCoordinates_norm_le
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (r : ℝ) (hr : 1 ≤ r) (a : realTypeSourceSubmodule 2) :
    ‖D.realSobolevCoordinates r hr a‖ ≤
      realSobolevEstimateConstant r*(1+‖a.val‖)^(2*r)*‖a.val‖ := by
  have hweight := SpectralWeight.piSobolev_realExtension_sixteen_le r
    (zero_le_one.trans hr) ‖a.val‖ (norm_nonneg a.val)
  calc
    _ ≤ 2048*(SpectralWeight.piSobolev r (zero_le_one.trans hr)).realExtension
        (16*‖a.val‖^2)*‖a.val‖ := D.m1Coordinates_norm_le _ _ a
    _ ≤ 2048*((1+17*Real.pi)^r*(1+‖a.val‖)^(2*r))*‖a.val‖ := by gcongr
    _ = _ := by unfold realSobolevEstimateConstant; ring

@[simp] theorem realSobolevCoordinates_zero
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (r : ℝ) (hr : 1 ≤ r) : D.realSobolevCoordinates r hr 0 = 0 := by
  exact D.m1Coordinates_zero _ _

end SourceBirkhoffMapComplexData

/-- Both conclusions of Corollary 23.5, simultaneously for every real order
s ≥ 1 and one constructed Birkhoff map, with the same positive constant. -/
theorem exists_sourceBirkhoffMap_corollary23_5 :
    ∃ W₀ B W : Set (CoeffPair 2), ∃ s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k,
      ∃ D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s,
        ∀ r : ℝ, ∀ hr : 1 ≤ r, ∃ c : ℝ, 0 < c ∧
          ∃ V : Set (CoeffPair 2), IsOpen V ∧ realTypeSourceLocus 2 ⊆ V ∧
            (∀ a ∈ V, Summable (sourceRealSobolevActionTerm r (zero_le_one.trans hr) a) ∧
              (∑' n : ℤ, sourceRealSobolevActionTerm r (zero_le_one.trans hr) a n) ≤
                c^2*(1+‖a‖)^(4*r)*‖a‖^2) ∧
            ∀ a : realTypeSourceSubmodule 2,
              ‖D.realSobolevCoordinates r hr a‖ ≤ c*(1+‖a.val‖)^(2*r)*‖a.val‖ := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic
    (by simp : (2:ℝ≥0∞) ≠ ⊤) (by norm_num : (1:ℝ≥0∞) < 2)
  refine ⟨W₀,B,W,s,D,?_⟩
  intro r hr
  obtain ⟨V,hV,hreal,hbound⟩ := exists_sourceRealSobolev_action_neighborhood r hr
  exact ⟨realSobolevEstimateConstant r,realSobolevEstimateConstant_pos r,V,hV,hreal,hbound,
    fun a => D.realSobolevCoordinates_norm_le r hr a⟩

end NLS.ZakharovShabat
