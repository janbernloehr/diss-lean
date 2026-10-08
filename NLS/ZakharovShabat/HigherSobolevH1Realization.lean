import NLS.ZakharovShabat.SourceH1ConverseActionEstimate
import NLS.ZakharovShabat.SourceSobolevHigherActionTrace

/-! # Coefficient-preserving H¹ realization of every higher Sobolev source -/
noncomputable section
namespace NLS.ZakharovShabat

/-- Forget higher regularity while retaining the physical H¹ source coefficients. -/
def higherSobolevToH1 (m : ℕ) (hm : 1 ≤ m) (a : SobolevSource m) :
    ScalarDomain 2 × ScalarDomain 2 :=
  (hierarchySobolevToScalarDomain m hm a.1, hierarchySobolevToScalarDomain m hm a.2)

@[simp] theorem sobolevSourceInclusion_higherSobolevToH1 (m : ℕ) (hm : 1 ≤ m)
    (a : SobolevSource m) :
    sobolevSourceInclusion (higherSobolevToH1 m hm a) = higherSobolevSourceInclusion m a := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext n
  · change (sobolevSourceInclusion _).fst n = (higherSobolevSourceInclusion m a).fst n
    simp [higherSobolevToH1]
  · change (sobolevSourceInclusion _).snd n = (higherSobolevSourceInclusion m a).snd n
    simp [higherSobolevToH1]

/-- The same potential on the original real H¹ locus. -/
def realHigherSobolevToH1 (m : ℕ) (hm : 1 ≤ m) (a : realTypeHigherSobolevSourceLocus m) :
    realTypeSobolevSourceLocus :=
  ⟨higherSobolevToH1 m hm a.val, by
    change IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion (higherSobolevToH1 m hm a.val)))
    rw [sobolevSourceInclusion_higherSobolevToH1]
    exact a.property⟩

@[simp] theorem sourceH1RealSource_realHigherSobolevToH1 (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    sourceH1RealSource (realHigherSobolevToH1 m hm a) =
      ⟨higherSobolevSourceInclusion m a.val,a.property⟩ := by
  apply Subtype.ext
  exact sobolevSourceInclusion_higherSobolevToH1 m hm a.val

/-- The realization has exactly the physical H¹ norm used by the localization theorem. -/
theorem sourcePhysicalH1Coordinates_higherSobolevToH1 (m : ℕ) (hm : 1 ≤ m) (a : SobolevSource m) :
    sourcePhysicalH1Coordinates (higherSobolevToH1 m hm a) = sourcePiSobolevCoordinates m 1 hm a := by
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext n
  · change (sourcePhysicalH1Coordinates _).fst n = (sourcePiSobolevCoordinates m 1 hm a).fst n
    rw [sourcePhysicalH1Coordinates_fst, sourcePiSobolevCoordinates_fst]
    simp [higherSobolevToH1]
  · change (sourcePhysicalH1Coordinates _).snd n = (sourcePiSobolevCoordinates m 1 hm a).snd n
    rw [sourcePhysicalH1Coordinates_snd, sourcePiSobolevCoordinates_snd]
    simp [higherSobolevToH1]

/-- Level-three real actions are summable at H¹ regularity. -/
theorem sourceH1_realThirdActions_summable (a : realTypeSobolevSourceLocus) :
    Summable (fun n : ℤ => sourceRealHigherAction (by simp) (by norm_num) (sourceH1RealSource a) n 2) := by
  obtain ⟨U,_,ha,h⟩ := exists_local_sourceSobolevHigherAction_trace a
  have hs := (h a.val ha).2.2 2 le_rfl
  change Summable (fun n : ℤ => ‖sourceComplexHigherAction (by simp) (by norm_num) n 2
    (sourceH1RealSource a).val‖) at hs
  have hh : Summable (fun n : ℤ => ‖sourceRealHigherAction (by simp) (by norm_num)
      (sourceH1RealSource a) n 2‖) := by
    simpa only [sourceComplexHigherAction_eq_real (φ := sourceH1RealSource a), Complex.norm_real] using hs
  exact hh.of_norm

/-- The summed third-level real action is the physical NLS energy, with its exact factor four. -/
theorem sourceH1_four_mul_sum_realThirdActions (a : realTypeSobolevSourceLocus) :
    4*(∑' n : ℤ, sourceRealHigherAction (by simp) (by norm_num) (sourceH1RealSource a) n 2) =
      (periodOneSobolevHamiltonian a.val).re := by
  have h := sourceSobolev_tsum_higherAction_three a
  change (∑' n : ℤ, sourceComplexHigherAction (by simp) (by norm_num) n 2
    (sourceH1RealSource a).val) = periodOneSobolevHamiltonian a.val/4 at h
  simp only [sourceComplexHigherAction_eq_real (φ := sourceH1RealSource a), ← Complex.ofReal_tsum] at h
  have hr := congrArg Complex.re h
  norm_num at hr
  linarith

end NLS.ZakharovShabat
