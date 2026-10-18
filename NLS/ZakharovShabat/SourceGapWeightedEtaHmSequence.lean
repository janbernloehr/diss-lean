import NLS.ZakharovShabat.SourceHmGapBounds
import NLS.ZakharovShabat.SourceGapWeightedEtaH1Sequence

/-! # The actual signed eta sequence at every integer Sobolev order

Both signs have the actual gap norm, including collapsed gaps. This
constructs the signed eta sequence in hm and bounds its norm by the
actual weighted gap sequence, without a fallback definition.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal


namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
include D

/-- The actual weighted gap sequence dominates each signed eta coefficient. -/
theorem gapWeightedEta_Hm_majorant (m : ℕ) (a : realTypeHigherSobolevSourceLocus m)
    (sign : ℂ) (hsign : sign = 1 ∨ sign = -1) (n : ℤ) :
    ‖((Weight.sobolev m n):ℂ)*sourceGapWeightedEtaCoordinate (by simp) (by norm_num)
      n s sign (higherSobolevSourceInclusion m a.val)‖ ≤ ‖sourceHmWeightedGapSequence m a.val n‖ := by
  have he := D.norm_gapWeightedEta_eq_gap ⟨higherSobolevSourceInclusion m a.val,a.property⟩ n sign hsign
  calc
    _ = (1+|(n:ℝ)|)^m*‖sourcePeriodicGapDisplacement (by simp) (by norm_num)
        (higherSobolevSourceInclusion m a.val) n‖ := by
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg ((Weight.sobolev m).positive n).le,he]
      simp only [Weight.sobolev_apply,Real.rpow_natCast]
    _ ≤ _ := sourceHmWeightedGapSequence_majorant m a.val n

/-- The actual signed eta sequence at every integer order. -/
def signedEtaHm (m : ℕ) (a : realTypeHigherSobolevSourceLocus m) (sign : ℂ) (hsign : sign = 1 ∨ sign = -1) :
    WeightedCoeff (Weight.sobolev m) 2 :=
  ⟨fun n => sourceGapWeightedEtaCoordinate (by simp) (by norm_num) n s sign (higherSobolevSourceInclusion m a.val),by
    change Memℓp (fun n => ((Weight.sobolev m n):ℂ)*sourceGapWeightedEtaCoordinate (by simp) (by norm_num)
      n s sign (higherSobolevSourceInclusion m a.val)) 2
    apply (lp.memℓp (sourceHmWeightedGapSequence m a.val)).mono'
    intro n
    exact D.gapWeightedEta_Hm_majorant m a sign hsign n⟩

@[simp] theorem signedEtaHm_apply (m : ℕ) (a : realTypeHigherSobolevSourceLocus m) (sign : ℂ)
    (hsign : sign = 1 ∨ sign = -1) (n : ℤ) :
    (D.signedEtaHm m a sign hsign).val n =
      sourceGapWeightedEtaCoordinate (by simp) (by norm_num) n s sign (higherSobolevSourceInclusion m a.val) := rfl

/-- The actual eta hm norm is bounded by the actual weighted gap norm. -/
theorem norm_signedEtaHm_le (m : ℕ) (a : realTypeHigherSobolevSourceLocus m) (sign : ℂ)
    (hsign : sign = 1 ∨ sign = -1) :
    ‖D.signedEtaHm m a sign hsign‖ ≤ ‖sourceHmWeightedGapSequence m a.val‖ := by
  change ‖WeightedCoeff.weightEquiv (Weight.sobolev m) 2 (D.signedEtaHm m a sign hsign)‖ ≤ _
  apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
  intro n
  exact D.gapWeightedEta_Hm_majorant m a sign hsign n


end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
