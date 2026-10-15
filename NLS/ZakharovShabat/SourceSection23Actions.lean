import NLS.ZakharovShabat.SourceSection22Original
import NLS.ZakharovShabat.SourceSobolevCommonConstants
import NLS.ZakharovShabat.SourceBirkhoffM1Coordinates
import NLS.ZakharovShabat.NormalizedWeightedSourceTopology

/-! # Original actions and exact norms for Section 23

The indexed actions agree with the original map's action radii throughout
its complex domain. Weighted normalization retains the literal physical
Fourier norm, including both components and the doubled frequency.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The original indexed action is the action in the actual map's radius identity. -/
theorem SourceSection17OriginalData.indexed_action_eq_complex
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p}
    {W₀ W V : Set (CoeffPair p)} {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (D : SourceSection17OriginalData hp hp1 W₀ W V s)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
    sourceIndexedAction hp hp1 n ψ = sourceComplexAction hp hp1 n ψ := by
  exact mul_left_cancel₀ (by norm_num : (2:ℂ) ≠ 0)
    ((D.indexed_action_radius ψ hψ n).symm.trans (D.complex.action_radius ψ hψ n))

/-- The literal weighted original indexed action, with physical frequency 2nπ. -/
def sourceIndexedWeightedActionTerm (φ : realTypeSourceSubmodule 2) (k : ℕ) (n : ℤ) : ℝ :=
  (1+|((2*n:ℤ):ℝ)*Real.pi|)^(2*k)*‖sourceIndexedAction (by simp) (by norm_num) n φ.val‖

/-- Original indexed actions agree with the retained real contour actions at every real source. -/
theorem sourceIndexedWeightedActionTerm_eq (φ : realTypeSourceSubmodule 2) (k : ℕ) (n : ℤ) :
    sourceIndexedWeightedActionTerm φ k n = sourceWeightedActionTerm φ k n := by
  simp only [sourceIndexedWeightedActionTerm,sourceWeightedActionTerm,
    sourceIndexedAction_eq_sourceRealAction (by simp) (by norm_num) n φ.val φ.property]

/-- Normalized weighted coordinates have exactly the source's physical weighted norm.
This is an equality with the literal absolutely convergent Fourier energy. -/
theorem normalizedWeightedSource_physical_norm (w : SpectralWeight) (a : CoeffPair 2) :
    Summable (fun n : ℤ => (w (2*n))^2*
      (‖(normalizedWeightedSource w a).fst n‖^2+‖(normalizedWeightedSource w a).snd n‖^2)) ∧
    ‖a‖^2 = ∑' n : ℤ, (w (2*n))^2*
      (‖(normalizedWeightedSource w a).fst n‖^2+‖(normalizedWeightedSource w a).snd n‖^2) := by
  have he (n : ℤ) : (w (2*n))^2*
      (‖(normalizedWeightedSource w a).fst n‖^2+‖(normalizedWeightedSource w a).snd n‖^2) =
        ‖a.fst n‖^2+‖a.snd n‖^2 := by
    simp only [normalizedWeightedSource_fst,normalizedWeightedSource_snd,norm_div,Complex.norm_real,
      Real.norm_of_nonneg (w.positive (2*n)).le]
    have hw : w (2*n) ≠ 0 := (w.positive (2*n)).ne'
    field_simp [hw]
  simp_rw [he]
  constructor
  · simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
      (a.fst.property.summable (by norm_num : 0 < (2:ℝ≥0∞).toReal)).add
        (a.snd.property.summable (by norm_num : 0 < (2:ℝ≥0∞).toReal))
  · simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using CoeffPair.norm_rpow_eq_tsum (by simp) a

namespace SourceSection17OriginalData
variable {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  (D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s)
include D

/-- The opening Parseval identity uses the component-sum Hilbert target norm. -/
theorem section23_parseval (φ : realTypeSourceSubmodule 2) :
    ‖WithLp.toLp 2 (sourceRealBirkhoffMap (by simp) (by norm_num) s φ)‖ = ‖φ.val‖ := by
  have h : ‖WithLp.toLp 2 (sourceRealBirkhoffMap (by simp) (by norm_num) s φ)‖^2 = ‖φ.val‖^2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    exact D.complex.hilbert_real_map_norm_sq φ
  nlinarith [norm_nonneg (WithLp.toLp 2 (sourceRealBirkhoffMap (by simp) (by norm_num) s φ)),
    norm_nonneg φ.val]

/-- The exact integer weighted target norm uses the same original indexed actions. -/
theorem section23_sobolev_norm_sq (m : ℕ) (hm : 1 ≤ m) (k : ℕ) (hk : k ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    ‖D.complex.sobolevCoordinates m hm k hk a‖^2 =
      2*(∑' n : ℤ, sourceIndexedWeightedActionTerm
        ⟨higherSobolevSourceInclusion m a.val,a.property⟩ k n) := by
  simp only [sourceIndexedWeightedActionTerm_eq]
  exact D.complex.sobolevCoordinates_norm_sq m hm k hk a

/-- Weighted target membership is constructive and its norm has the literal original action sum. -/
theorem section23_weighted_norm_sq (w : SpectralWeight) (hw : w.HasLinearFactor)
    (a : realTypeSourceSubmodule 2) :
    ‖D.complex.m1Coordinates w hw a‖^2 =
      2*(∑' n : ℤ, (w (2*n))^2*
        ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a.val)‖) := by
  have hreal := normalizedWeightedSource_realType w a.val a.property
  simp only [sourceIndexedAction_eq_sourceRealAction (by simp) (by norm_num) _ _ hreal,
    D.complex.m1Coordinates_norm_sq,sourceM1ActionTerm,
    sourceComplexAction_eq_sourceRealAction (by simp) (by norm_num) _ _ hreal]
end SourceSection17OriginalData
end NLS.ZakharovShabat
