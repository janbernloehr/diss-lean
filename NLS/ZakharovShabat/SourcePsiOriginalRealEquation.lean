import NLS.ZakharovShabat.SourcePsiOriginalJacobian
import NLS.SequenceSpaces.DeletedRealEquiv

/-!
# The original equation on the real deleted Banach space

Taking real parts after complex inclusion defines the real equation.
At real-type sources it agrees exactly with the original complex
equation. Its real derivative is the restriction of the actual complex
root Jacobian.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original equation restricted to real root displacements. -/
def sourcePsiOriginalRealEquation (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a : RealDeletedCoeff p n) (ψ : CoeffPair p) : RealDeletedCoeff p n :=
  RealDeletedCoeff.reCLM n (sourcePsiOriginalEquation hp hp1 n (RealDeletedCoeff.complexCLM n a) ψ)

/-- The actual Fréchet derivative of the real equation in its root variable. -/
def sourcePsiOriginalRealRootJacobian (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (a : RealDeletedCoeff p n) (ψ : CoeffPair p) : RealDeletedCoeff p n →L[ℝ] RealDeletedCoeff p n :=
  fderiv ℝ (fun b : RealDeletedCoeff p n => sourcePsiOriginalRealEquation hp hp1 n b ψ) a

theorem SourceLemma12_4Data.originalRealEquation_hasFDerivAt
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (ψ : CoeffPair p) (hψW : ψ ∈ W)
    (n : ℤ) (a : RealDeletedCoeff p n) :
    HasFDerivAt (fun b : RealDeletedCoeff p n => sourcePsiOriginalRealEquation hp hp1 n b ψ)
      ((RealDeletedCoeff.reCLM n).comp
        (((sourcePsiOriginalRootJacobian hp hp1 n (RealDeletedCoeff.complexCLM n a) ψ).restrictScalars ℝ).comp
          (RealDeletedCoeff.complexCLM n))) a := by
  exact (RealDeletedCoeff.reCLM n).hasFDerivAt.comp a
    (((H.originalRootJacobian_hasFDerivAt ψ hψW n (RealDeletedCoeff.complexCLM n a)).restrictScalars ℝ).comp
      a (RealDeletedCoeff.complexCLM n).hasFDerivAt)

theorem SourceLemma12_4Data.originalRealRootJacobian_eq
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (ψ : CoeffPair p) (hψW : ψ ∈ W)
    (n : ℤ) (a : RealDeletedCoeff p n) :
    sourcePsiOriginalRealRootJacobian hp hp1 n a ψ =
      (RealDeletedCoeff.reCLM n).comp
        (((sourcePsiOriginalRootJacobian hp hp1 n (RealDeletedCoeff.complexCLM n a) ψ).restrictScalars ℝ).comp
          (RealDeletedCoeff.complexCLM n)) :=
  (H.originalRealEquation_hasFDerivAt ψ hψW n a).fderiv

theorem SourceLemma12_4Data.originalRealEquation_complex
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (ψ : CoeffPair p) (hψW : ψ ∈ W)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n : ℤ) (a : RealDeletedCoeff p n) :
    RealDeletedCoeff.complexCLM n (sourcePsiOriginalRealEquation hp hp1 n a ψ) =
      sourcePsiOriginalEquation hp hp1 n (RealDeletedCoeff.complexCLM n a) ψ := by
  apply RealDeletedCoeff.complex_re
  exact H.real ψ hψW hreal n _ (RealDeletedCoeff.complex_real n a)

end NLS.ZakharovShabat
