import NLS.SequenceSpaces.ConjugateReflection
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-! # The physical real form of a symmetric weighted Fourier space

Physical real-valuedness is conjugate reflection, not coefficientwise
reality. Its fixed space is a closed real Banach subspace. The continuous
real-part projection and exact complex decomposition retain the original
weighted norm and every Fourier coefficient.
-/
noncomputable section
open Set Complex
open scoped ENNReal ComplexConjugate
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

def physicalRealSubmodule (w : Weight) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Submodule ℝ (WeightedCoeff w p) where
  carrier := {a | ∀ k, a.val k = conj (a.val (-k))}
  zero_mem' := by intro k; simp
  add_mem' := by
    intro a b ha hb k
    change a.val k+b.val k = conj (a.val (-k)+b.val (-k))
    rw [map_add,ha k,hb k]
  smul_mem' := by
    intro r a ha k
    change (r : ℂ)*a.val k = conj ((r : ℂ)*a.val (-k))
    rw [map_mul,Complex.conj_ofReal,ha k]

theorem isClosed_physicalRealSubmodule (w : Weight) :
    IsClosed (physicalRealSubmodule w p : Set (WeightedCoeff w p)) := by
  change IsClosed {a : WeightedCoeff w p | ∀ k, a.val k = conj (a.val (-k))}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro k
  exact isClosed_eq (evalCLM w p k).continuous
    (Complex.conjCLE.continuous.comp (evalCLM w p (-k)).continuous)

instance physicalRealSubmoduleComplete (w : Weight) [CompleteSpace (WeightedCoeff w p)] :
    CompleteSpace (physicalRealSubmodule w p) :=
  (isClosed_physicalRealSubmodule w).completeSpace_coe

def conjugateReflectionRealCLM (w : Weight) (hw : ∀ k, w (-k) = w k) :
    WeightedCoeff w p →L[ℝ] WeightedCoeff w p :=
  LinearMap.mkContinuous
    { toFun := conjugateReflection w hw
      map_add' := by
        intro a b
        apply Subtype.ext
        funext k
        change (conjugateReflection w hw (a+b)).val k =
          (conjugateReflection w hw a).val k+(conjugateReflection w hw b).val k
        simp only [conjugateReflection_apply]
        exact map_add (starRingEnd ℂ) (a.val (-k)) (b.val (-k))
      map_smul' := by
        intro r a
        apply Subtype.ext
        funext k
        change (conjugateReflection w hw (r • a)).val k =
          ((r : ℂ)*(conjugateReflection w hw a).val k)
        rw [conjugateReflection_apply,conjugateReflection_apply]
        change conj ((r : ℂ)*a.val (-k)) = _
        rw [map_mul,Complex.conj_ofReal] }
    1 (by
      intro a
      change ‖conjugateReflection w hw a‖ ≤ 1*‖a‖
      rw [norm_conjugateReflection,one_mul])

@[simp] theorem conjugateReflectionRealCLM_apply (w : Weight) (hw : ∀ k, w (-k) = w k)
    (a : WeightedCoeff w p) (k : ℤ) :
    (conjugateReflectionRealCLM w hw a).val k = conj (a.val (-k)) :=
  conjugateReflection_apply w hw a k

def physicalRealPart (w : Weight) (hw : ∀ k, w (-k) = w k) :
    WeightedCoeff w p →L[ℝ] physicalRealSubmodule w p :=
  ((1/2 : ℝ) • (ContinuousLinearMap.id ℝ (WeightedCoeff w p)+conjugateReflectionRealCLM w hw)).codRestrict
    (physicalRealSubmodule w p) (by
      intro a k
      change ((1/2 : ℝ) : ℂ)*(a.val k+(conjugateReflectionRealCLM w hw a).val k) =
        conj (((1/2 : ℝ) : ℂ)*(a.val (-k)+(conjugateReflectionRealCLM w hw a).val (-k)))
      simp only [conjugateReflectionRealCLM_apply,map_mul,map_add,Complex.conj_ofReal,
        neg_neg,Complex.conj_conj]
      ring)

theorem physicalRealPart_apply (w : Weight) (hw : ∀ k, w (-k) = w k)
    (a : WeightedCoeff w p) (k : ℤ) :
    (physicalRealPart w hw a).val.val k = (a.val k+conj (a.val (-k)))/2 := by
  change ((1/2 : ℝ) : ℂ)*(a.val k+(conjugateReflectionRealCLM w hw a).val k) = _
  rw [conjugateReflectionRealCLM_apply]
  push_cast
  ring

theorem physicalRealPart_real (w : Weight) (hw : ∀ k, w (-k) = w k)
    (a : physicalRealSubmodule w p) : physicalRealPart w hw a.val = a := by
  apply Subtype.ext
  apply Subtype.ext
  funext k
  rw [physicalRealPart_apply,← a.property k]
  ring

theorem physicalRealPart_complex_decomp (w : Weight) (hw : ∀ k, w (-k) = w k)
    (a : WeightedCoeff w p) :
    a = (physicalRealPart w hw a).val+I • (physicalRealPart w hw ((-I) • a)).val := by
  apply Subtype.ext
  funext k
  change a.val k = (physicalRealPart w hw a).val.val k+
    I*(physicalRealPart w hw ((-I) • a)).val.val k
  rw [physicalRealPart_apply,physicalRealPart_apply]
  change a.val k = (a.val k+conj (a.val (-k)))/2+
    I*(((-I)*a.val k+conj ((-I)*a.val (-k)))/2)
  rw [map_mul,map_neg,Complex.conj_I,neg_neg]
  linear_combination ((a.val k-conj (a.val (-k)))/2)*Complex.I_sq

end NLS.WeightedCoeff
