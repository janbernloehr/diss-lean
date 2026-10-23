import NLS.ZakharovShabat.SourceSymmetricSignedGaps
import NLS.SequenceSpaces.RealCoeff

/-! # Real Fourier coordinates on the reflection-symmetric source slice

The second Fourier component supplies real sequence coordinates. Reversing
its indices gives the first component. This parametrization is continuous
and real linear and has exactly the reflection-fixed real-type sources as
its range, with an explicit continuous left inverse.
-/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A real sequence is the second component of a symmetric source, with reversed first component. -/
def symmetricSourceCoefficients (p : ℝ≥0∞) [Fact (1 ≤ p)] : RealCoeff p →L[ℝ] CoeffPair p :=
  ((CoeffPair.toMax p).symm.toContinuousLinearMap.restrictScalars ℝ).comp
    ((((Coeff.reflection (p := p)).toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp
      (RealCoeff.complexCLM p)).prod (RealCoeff.complexCLM p))

@[simp] theorem symmetricSourceCoefficients_fst (a : RealCoeff p) (n : ℤ) :
    (symmetricSourceCoefficients p a).fst n = (a (-n) : ℂ) := rfl

@[simp] theorem symmetricSourceCoefficients_snd (a : RealCoeff p) (n : ℤ) :
    (symmetricSourceCoefficients p a).snd n = (a n : ℂ) := rfl

theorem symmetricSourceCoefficients_realType (a : RealCoeff p) :
    IsRealType (CoeffPair.toMax p (symmetricSourceCoefficients p a)) := by
  intro n
  change (a n : ℂ) = conj (a (-(-n)) : ℂ)
  simp

/-- The parametrization lands in the actual real-type source subspace. -/
def symmetricRealSourceCoefficients (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    RealCoeff p →L[ℝ] realTypeSourceSubmodule p :=
  (symmetricSourceCoefficients p).codRestrict _ symmetricSourceCoefficients_realType

@[simp] theorem symmetricRealSourceCoefficients_val (a : RealCoeff p) :
    (symmetricRealSourceCoefficients p a).val = symmetricSourceCoefficients p a := rfl

/-- Every parametrized source is fixed by the actual spatial reflection. -/
theorem symmetricRealSourceCoefficients_reflection_fixed (a : RealCoeff p) :
    realSourceSpatialReflection (symmetricRealSourceCoefficients p a) =
      symmetricRealSourceCoefficients p a := by
  apply Subtype.ext
  apply (sourceSpatialReflection_eq_self_iff _ (symmetricSourceCoefficients_realType a)).mpr
  intro n
  simp

/-- The second real Fourier component is an explicit left inverse of the parametrization. -/
theorem re_snd_symmetricSourceCoefficients (a : RealCoeff p) :
    Coeff.reCLM p (symmetricSourceCoefficients p a).snd = a := by
  ext n
  simp

theorem symmetricRealSourceCoefficients_injective :
    Function.Injective (symmetricRealSourceCoefficients p) := by
  intro a b he
  have h := congrArg (fun φ : realTypeSourceSubmodule p => Coeff.reCLM p φ.val.snd) he
  simpa only [symmetricRealSourceCoefficients_val,re_snd_symmetricSourceCoefficients] using h

/-- The coordinates reconstruct every actual reflection-fixed real source. -/
theorem symmetricRealSourceCoefficients_reconstruct (φ : realTypeSourceSubmodule p)
    (hφ : realSourceSpatialReflection φ = φ) :
    symmetricRealSourceCoefficients p (Coeff.reCLM p φ.val.snd) = φ := by
  have href : sourceSpatialReflection φ.val = φ.val := congrArg Subtype.val hφ
  have hreal := (sourceSpatialReflection_eq_self_iff φ.val φ.property).mp href
  have hs (n : ℤ) : φ.val.snd n = φ.val.fst (-n) :=
    (φ.property n).trans (hreal (-n))
  have hsim (n : ℤ) : (φ.val.snd n).im = 0 := by
    rw [hs n]
    exact Complex.conj_eq_iff_im.mp (hreal (-n))
  apply Subtype.ext
  apply (CoeffPair.toMax p).injective
  apply Prod.ext
  · ext n
    change ((φ.val.snd (-n)).re : ℂ) = φ.val.fst n
    calc
      ((φ.val.snd (-n)).re : ℂ) = φ.val.snd (-n) :=
        Complex.ext rfl (by simpa only [ofReal_im] using (hsim (-n)).symm)
      _ = φ.val.fst n := by simpa using hs (-n)
  · ext n
    change ((φ.val.snd n).re : ℂ) = φ.val.snd n
    exact Complex.ext rfl (by simpa only [ofReal_im] using (hsim n).symm)

/-- The range is exactly the reflection-fixed real-type slice. -/
theorem range_symmetricRealSourceCoefficients :
    Set.range (symmetricRealSourceCoefficients p) =
      {φ : realTypeSourceSubmodule p | realSourceSpatialReflection φ = φ} := by
  ext φ
  constructor
  · rintro ⟨a,rfl⟩
    exact symmetricRealSourceCoefficients_reflection_fixed a
  · intro hφ
    exact ⟨Coeff.reCLM p φ.val.snd,symmetricRealSourceCoefficients_reconstruct φ hφ⟩

/-- The actual signed-gap map in real Fourier coordinates. -/
def symmetricSourceSignedGapMap (hp : p ≠ ⊤) (hp1 : 1 < p) : RealCoeff p → RealCoeff p :=
  fun a => Coeff.reCLM p (sourceSignedGapSequence hp hp1 (symmetricSourceCoefficients p a))

@[simp] theorem symmetricSourceSignedGapMap_apply (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : RealCoeff p) (n : ℤ) :
    symmetricSourceSignedGapMap hp hp1 a n =
      (sourceSignedGapSequence hp hp1 (symmetricSourceCoefficients p a) n).re := rfl

/-- The real-coordinate signed-gap map is real analytic everywhere. -/
theorem analyticAt_symmetricSourceSignedGapMap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : RealCoeff p) : AnalyticAt ℝ (symmetricSourceSignedGapMap hp hp1) a := by
  obtain ⟨W,_,hreal,hseq⟩ := exists_sourceSignedGapSequence_analytic_common_domain hp hp1
  have h : AnalyticAt ℝ (sourceSignedGapSequence hp hp1) (symmetricSourceCoefficients p a) :=
    (hseq _ (hreal (symmetricSourceCoefficients_realType a))).restrictScalars
  exact ((Coeff.reCLM p).analyticAt _).comp
    (h.comp ((symmetricSourceCoefficients p).analyticAt a))

end NLS.ZakharovShabat
