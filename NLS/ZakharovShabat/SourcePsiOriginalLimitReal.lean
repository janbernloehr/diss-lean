import NLS.ZakharovShabat.SourcePsiOriginalLimitInjectivity
import NLS.SequenceSpaces.RealCoeff

/-!
# The original limiting Jacobian on real coefficient sequences

The full limiting Jacobian preserves real sequences throughout the original
real root-placement domain. Its bounded real restriction is compatible with
the complex inclusion on every input, so the real operator uses the same
matrix entries and contour normalization as the intrinsic complex limit.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The bounded real restriction of the intrinsic original limit Jacobian. -/
def sourcePsiOriginalLimitRealOperator (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : RealCoeff p) (φ : realTypeSourceSubmodule p) :
    RealCoeff p →L[ℝ] RealCoeff p :=
  (Coeff.reCLM p).comp
    (((sourcePsiOriginalLimitOperator hp hp1 (RealCoeff.complexCLM p a) φ).restrictScalars ℝ).comp
      (RealCoeff.complexCLM p))

/-- The actual limiting operator maps every real coefficient vector to a real vector. -/
theorem SourceLemma12_4Data.originalLimitOperator_preserves_real
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφW : φ ∈ W) (hφV : φ ∈ V)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (a : Coeff p) (ha : a ∈ sourcePsiOriginalRootPlacement D)
    (haReal : ∀ k : ℤ, (a k).im = 0)
    (h : Coeff p) (hhReal : ∀ k : ℤ, (h k).im = 0) (m : ℤ) :
    (sourcePsiOriginalLimitOperator hp hp1 a φ h m).im = 0 := by
  have hh : star h = h := by
    ext k
    exact Complex.conj_eq_iff_im.mpr (hhReal k)
  have he := Coeff.operator_star_of_real_entries hp
    (sourcePsiOriginalLimitOperator hp hp1 a φ)
    (H.originalLimitOperator_entry_real hD φ hφW hφV hφ a ha haReal) h
  rw [hh] at he
  exact Complex.conj_eq_iff_im.mp (congrArg (fun b : Coeff p => b m) he.symm)

/-- Complex inclusion intertwines the bounded real restriction with the actual limit operator. -/
theorem SourceLemma12_4Data.originalLimitRealOperator_complex
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (H : SourceLemma12_4Data hp hp1 W)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : realTypeSourceSubmodule p) (hφW : (φ:CoeffPair p) ∈ W)
    (hφV : (φ:CoeffPair p) ∈ V)
    (a : RealCoeff p) (ha : RealCoeff.complexCLM p a ∈ sourcePsiOriginalRootPlacement D)
    (h : RealCoeff p) :
    RealCoeff.complexCLM p (sourcePsiOriginalLimitRealOperator hp hp1 a φ h) =
      sourcePsiOriginalLimitOperator hp hp1 (RealCoeff.complexCLM p a) φ (RealCoeff.complexCLM p h) := by
  apply RealCoeff.complexCLM_reCLM
  exact H.originalLimitOperator_preserves_real hD φ hφW hφV φ.property
    (RealCoeff.complexCLM p a) ha (fun k => by simp)
    (RealCoeff.complexCLM p h) (fun k => by simp)

end NLS.ZakharovShabat
