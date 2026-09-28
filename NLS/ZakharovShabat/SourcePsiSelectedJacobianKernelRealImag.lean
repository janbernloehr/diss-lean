import NLS.ZakharovShabat.SourcePsiGlobalRealJacobian
import NLS.ZakharovShabat.SourcePsiSelectedJacobianEntry
import NLS.SequenceSpaces.DeletedRealOperator

/-!
# Real and imaginary parts of a selected psi-Jacobian kernel direction

On a real-type source and real displaced-root base point, the selected
psi equation has real root-direction matrix entries. The bounded
Jacobian therefore preserves pointwise conjugation, so both real and
imaginary parts of any complex kernel direction remain in its kernel.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem sourcePsiSelectedRootJacobian_real_matrix_entries
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p))
    (hUopen : IsOpen U)
    (hdiff : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U)
    (hrealSeq : ∀ t ∈ U,
      IsRealType (CoeffPair.toMax p t.2) →
      (∀ j : ℤ, (displacedRoots (t.1 : Coeff p) j).im = 0) →
        ∀ m : ℤ,
          ((sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 :
            Coeff p) m).im = 0)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (hpair : (a,ψ) ∈ U)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (hroots : ∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0) :
    ∀ m k : ℤ,
      (Coeff.deletedOperatorMatrixEntry n
        (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ) m k).im = 0 := by
  intro m k
  by_cases hkn : k = n
  · subst k
    simp
  · rw [Coeff.deletedOperatorMatrixEntry_apply_other n m k hkn]
    rw [sourcePsiSelectedRootJacobian_entry_eq_deriv
      hp hp1 n c R U hUopen hdiff a ψ hpair m k hkn]
    exact deriv_sourcePsiSelectedEquationSequence_im_eq_zero
      hp hp1 n a ψ hψ hroots c R U hUopen hpair hrealSeq hdiff m k hkn

/-- A complex kernel direction splits into two real kernel directions
for the actual bounded selected psi-Jacobian. -/
theorem sourcePsiSelectedRootJacobian_kernel_realImag
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (U : Set (DeletedCoeff p n × CoeffPair p))
    (hUopen : IsOpen U)
    (hdiff : DifferentiableOn ℂ
      (fun t : DeletedCoeff p n × CoeffPair p =>
        sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2) U)
    (hrealSeq : ∀ t ∈ U,
      IsRealType (CoeffPair.toMax p t.2) →
      (∀ j : ℤ, (displacedRoots (t.1 : Coeff p) j).im = 0) →
        ∀ m : ℤ,
          ((sourcePsiSelectedEquationSequence hp hp1 n c R t.1 t.2 :
            Coeff p) m).im = 0)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (hpair : (a,ψ) ∈ U)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (hroots : ∀ j : ℤ, (displacedRoots (a : Coeff p) j).im = 0)
    (h : DeletedCoeff p n)
    (hkernel : sourcePsiSelectedRootJacobian hp hp1 n c R a ψ h = 0) :
    sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
      (DeletedCoeff.realPart h) = 0 ∧
    sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
      (DeletedCoeff.imagPart h) = 0 := by
  exact Coeff.deletedOperator_kernel_realImag_of_real_entries hp n
    (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ)
    (sourcePsiSelectedRootJacobian_real_matrix_entries
      hp hp1 n c R U hUopen hdiff hrealSeq a ψ hpair hψ hroots)
    h hkernel

end NLS.ZakharovShabat
