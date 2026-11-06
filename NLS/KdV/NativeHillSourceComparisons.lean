import NLS.KdV.NativeHillContinuousSource
import NLS.SequenceSpaces.PhysicalRealMeanZeroWeighted
import NLS.KdV.NativeHillPhysicalDirection
import NLS.Fourier.SobolevContinuousJetDerivative

/-! # Physical source compatibility and continuity on the native Sobolev scale -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.Fourier NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV

/-- Equality of literal native Fourier coefficients gives equality of the
ENTIRE original physical Hill source across arbitrary native orders. -/
theorem nativeHillPhysicalSource_eq_of_coefficients (s t : ℕ) (q : ScalarSobolev s) (p : ScalarSobolev t)
    (hq : ∀ j : ℤ, q.val (-j)=conj (q.val j)) (hp : ∀ j : ℤ, p.val (-j)=conj (p.val j))
    (he : ∀ j : ℤ, q.val j=p.val j) :
    nativeHillPhysicalSource s q hq=nativeHillPhysicalSource t p hp := by
  apply Subtype.ext
  apply Subtype.ext
  funext j
  rw [←SpectralWeight.toCoeff_apply,←SpectralWeight.toCoeff_apply,
    nativeHillPhysicalSource_toCoeff,nativeHillPhysicalSource_toCoeff]
  have hab : WeightedCoeff.sobolevToL2 (Nat.cast_nonneg s) q=
      WeightedCoeff.sobolevToL2 (Nat.cast_nonneg t) p := by
    ext n
    simp only [WeightedCoeff.sobolevToL2_apply,he]
  rw [hab]

/-- The canonical physical source is continuous in every original native norm. -/
theorem continuous_nativeHillPhysicalSource (s : ℕ) :
    Continuous (fun q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (s : ℝ)) =>
      nativeHillPhysicalSource s q.val q.property.1) := by
  apply Continuous.subtype_mk
  have he : (fun q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (s : ℝ)) =>
      (nativeHillPhysicalSource s q.val q.property.1).val) = fun q => nativeHillPhysicalDirection s q.val :=
    funext (fun q => (nativeHillPhysicalDirection_eq_source s q.val q.property.1).symm)
  have hc : Continuous (fun q : physicalRealMeanZeroWeightedSubmodule (Weight.sobolev (s : ℝ)) =>
      nativeHillPhysicalDirection s q.val) :=
    (nativeHillPhysicalDirection s).continuous.comp continuous_subtype_val
  rw [←he] at hc
  exact hc

/-- The canonical continuous representative is a bounded native map. -/
theorem continuous_nativeHillContinuousSource (s : ℕ) (hs : 1≤s) :
    Continuous (nativeHillContinuousSource s hs) :=
  periodOneSobolevSynthesis.continuous.comp (hierarchySobolevToScalarDomain s hs).continuous

/-- Every continuous native realization with the same coefficients agrees,
also when its two native regularity indices differ. -/
theorem nativeHillContinuousSource_eq_of_native_coefficients (s t : ℕ) (hs : 1≤s) (ht : 1≤t)
    (q : ScalarSobolev s) (p : ScalarSobolev t) (he : ∀ j : ℤ, q.val j=p.val j) :
    nativeHillContinuousSource s hs q=nativeHillContinuousSource t ht p := by
  apply ContinuousMap.ext
  intro x
  obtain ⟨y,rfl⟩ := QuotientAddGroup.mk_surjective x
  have hf := nativeHillContinuousSource_eq_of_coefficients s hs q _
    (continuous_periodOneSobolevSynthesis _) (nativeHillContinuousSource_periodic t ht p)
    (fun j => (he j).trans (nativeHillContinuousSource_coefficient t ht p j).symm)
  exact congrFun hf y

/-- The canonical continuous source is the zeroth bounded continuous jet. -/
theorem nativeHillContinuousSource_eq_zero_jet (s : ℕ) (hs : 1≤s) (q : ScalarSobolev s) :
    nativeHillContinuousSource s hs q=hierarchySobolevJetContinuous s 0 (by omega) q := rfl

/-- The second classical derivative is a bounded continuous jet whenever
three native derivatives are available; no smoothness is assumed. -/
theorem iteratedDeriv_nativeHillContinuousSource_two (s : ℕ) (hs : 3≤s) (q : ScalarSobolev s) :
    iteratedDeriv 2 (fun x : ℝ => nativeHillContinuousSource s (by omega) q (x : AddCircle (2 : ℝ))) =
      fun x : ℝ => hierarchySobolevJetContinuous s 2 (by omega) q (x : AddCircle (2 : ℝ)) := by
  simp only [nativeHillContinuousSource_eq_zero_jet]
  exact iteratedDeriv_hierarchySobolevJetContinuous s (by omega) q 2 (by omega)

end NLS.KdV
