import NLS.SequenceSpaces.DeletedRealOperator
import NLS.SequenceSpaces.RealCoeff

/-!
# The real deleted sequence space and restriction of equivalences

Real lp sequences with one omitted coordinate form the real parameter
space. Inclusion and real-part maps connect it to the complex deleted
space. A continuous complex equivalence preserving real inputs in both
directions restricts to a continuous real linear equivalence.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Real lp sequences whose omitted coordinate is zero. -/
abbrev RealDeletedCoeff (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : ℤ) :=
  (lp.evalCLM ℝ (fun _ : ℤ => ℝ) p n).ker

namespace RealDeletedCoeff

instance (n : ℤ) : CompleteSpace (RealDeletedCoeff p n) := inferInstance

/-- Coordinatewise complex inclusion on the deleted space. -/
def complexCLM (n : ℤ) : RealDeletedCoeff p n →L[ℝ] DeletedCoeff p n :=
  ((RealCoeff.complexCLM p).comp (lp.evalCLM ℝ (fun _ : ℤ => ℝ) p n).ker.subtypeL).codRestrict
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.restrictScalars ℝ) (by
      intro a
      change ((RealCoeff.complexCLM p) (a:RealCoeff p)) n = 0
      simp only [RealCoeff.complexCLM_apply,show (a:RealCoeff p) n = 0 from a.property,Complex.ofReal_zero])

/-- Coordinatewise real part on the deleted space. -/
def reCLM (n : ℤ) : DeletedCoeff p n →L[ℝ] RealDeletedCoeff p n :=
  ((Coeff.reCLM p).comp ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL.restrictScalars ℝ)).codRestrict
    (lp.evalCLM ℝ (fun _ : ℤ => ℝ) p n).ker (by
      intro a
      change (Coeff.reCLM p (a:Coeff p)) n = 0
      simp only [Coeff.reCLM_apply,show (a:Coeff p) n = 0 from a.property,Complex.zero_re])

@[simp] theorem complexCLM_apply (n : ℤ) (a : RealDeletedCoeff p n) (m : ℤ) :
    (complexCLM n a : Coeff p) m = ((a : RealCoeff p) m : ℂ) := rfl

@[simp] theorem reCLM_apply (n : ℤ) (a : DeletedCoeff p n) (m : ℤ) :
    (reCLM n a : RealCoeff p) m = ((a : Coeff p) m).re := rfl

theorem re_complex (n : ℤ) (a : RealDeletedCoeff p n) : reCLM n (complexCLM n a) = a :=
  Subtype.ext (RealCoeff.reCLM_complexCLM p (a:RealCoeff p))

theorem complex_re (n : ℤ) (a : DeletedCoeff p n) (ha : ∀ m : ℤ, ((a:Coeff p) m).im = 0) :
    complexCLM n (reCLM n a) = a :=
  Subtype.ext (RealCoeff.complexCLM_reCLM p (a:Coeff p) ha)

theorem complex_real (n : ℤ) (a : RealDeletedCoeff p n) (m : ℤ) :
    ((complexCLM n a:Coeff p) m).im = 0 := by
  change (((a:RealCoeff p) m:ℂ)).im = 0
  simp

/-- Forget the unused real coordinate, compatibly with complex deletion. -/
def deleteCoordinateTo (n : ℤ) : RealCoeff p →L[ℝ] RealDeletedCoeff p n :=
  (reCLM n).comp (((Coeff.deleteCoordinateTo n).restrictScalars ℝ).comp (RealCoeff.complexCLM p))

theorem complex_deleteCoordinateTo (n : ℤ) (a : RealCoeff p) :
    complexCLM n (deleteCoordinateTo n a) = Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p a) := by
  change complexCLM n (reCLM n (Coeff.deleteCoordinateTo n (RealCoeff.complexCLM p a))) = _
  apply complex_re
  intro m
  change ((Coeff.deleteCoordinate n (RealCoeff.complexCLM p a)) m).im = 0
  by_cases hmn : m = n
  · subst m
    simp
  · rw [Coeff.deleteCoordinate_apply_other n m hmn]
    simp

/-- Restrict an equivalence and its real-preserving inverse to real sequences. -/
def restrictEquiv (n : ℤ) (e : DeletedCoeff p n ≃L[ℂ] DeletedCoeff p n)
    (hr : ∀ a : DeletedCoeff p n, (∀ m : ℤ, ((a:Coeff p) m).im = 0) →
      ∀ m : ℤ, ((e a:Coeff p) m).im = 0)
    (hi : ∀ a : DeletedCoeff p n, (∀ m : ℤ, ((a:Coeff p) m).im = 0) →
      ∀ m : ℤ, ((e.symm a:Coeff p) m).im = 0) :
    RealDeletedCoeff p n ≃L[ℝ] RealDeletedCoeff p n := by
  let A := (reCLM (p := p) n).comp ((e.toContinuousLinearMap.restrictScalars ℝ).comp (complexCLM n))
  let B := (reCLM (p := p) n).comp ((e.symm.toContinuousLinearMap.restrictScalars ℝ).comp (complexCLM n))
  exact
    { toLinearEquiv :=
        { A.toLinearMap with
          invFun := B
          left_inv := by
            intro a
            change reCLM n (e.symm (complexCLM n (reCLM n (e (complexCLM n a))))) = a
            rw [complex_re n _ (hr _ (complex_real n a)),e.symm_apply_apply,re_complex]
          right_inv := by
            intro a
            change reCLM n (e (complexCLM n (reCLM n (e.symm (complexCLM n a))))) = a
            rw [complex_re n _ (hi _ (complex_real n a)),e.apply_symm_apply,re_complex] }
      continuous_toFun := A.continuous
      continuous_invFun := B.continuous }

theorem complex_restrictEquiv (n : ℤ) (e : DeletedCoeff p n ≃L[ℂ] DeletedCoeff p n)
    (hr : ∀ a : DeletedCoeff p n, (∀ m : ℤ, ((a:Coeff p) m).im = 0) →
      ∀ m : ℤ, ((e a:Coeff p) m).im = 0)
    (hi : ∀ a : DeletedCoeff p n, (∀ m : ℤ, ((a:Coeff p) m).im = 0) →
      ∀ m : ℤ, ((e.symm a:Coeff p) m).im = 0) (b : RealDeletedCoeff p n) :
    complexCLM n (restrictEquiv n e hr hi b) = e (complexCLM n b) :=
  complex_re n _ (hr _ (complex_real n b))

end RealDeletedCoeff

end NLS
