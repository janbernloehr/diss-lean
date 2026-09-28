import NLS.SequenceSpaces.DeletedOperatorExtension
import NLS.ZakharovShabat.SourcePsiGapRootDerivative

/-!
# Selected psi Jacobians on one common sequence space

Lemma 12.10 views each deleted-index Jacobian as an operator on the
full `ℓᵖ` space by putting `2` on its omitted diagonal entry and zero
in the other entries of that row and column. This makes operators with
different deleted indices comparable in operator norm.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Extend the selected root Jacobian to the full coefficient space
using the dissertation's diagonal value `2` at index `n`. -/
def sourcePsiFullRootJacobian
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) :
    Coeff p →L[ℂ] Coeff p :=
  Coeff.deletedJacobianExtension n
    (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ)

/-- The omitted output row is multiplication by two. -/
theorem sourcePsiFullRootJacobian_deletedRow
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (h : Coeff p) :
    (sourcePsiFullRootJacobian hp hp1 n c R a ψ h) n = 2*h n := by
  exact Coeff.deletedOperatorExtension_apply_same n 2
    (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ) h

/-- The omitted input column has no retained output entries. -/
theorem sourcePsiFullRootJacobian_deletedColumn
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) (t : ℂ) :
    sourcePsiFullRootJacobian hp hp1 n c R a ψ (lp.single p n t) =
      lp.single p n (2*t) := by
  exact Coeff.deletedOperatorExtension_single_same n 2 t
    (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ)

/-- The extension agrees with the selected Jacobian on every
retained input vector. -/
theorem sourcePsiFullRootJacobian_apply_deleted
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (a h : DeletedCoeff p n) (ψ : CoeffPair p) :
    sourcePsiFullRootJacobian hp hp1 n c R a ψ (h : Coeff p) =
      (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ h : Coeff p) := by
  exact Coeff.deletedOperatorExtension_apply_deleted n 2
    (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ) h

/-- At any parameter point, the full and deleted Jacobians are
bijective together. -/
theorem sourcePsiFullRootJacobian_bijective_iff
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) :
    Function.Bijective (sourcePsiFullRootJacobian hp hp1 n c R a ψ) ↔
      Function.Bijective (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ) :=
  Coeff.deletedJacobianExtension_bijective_iff n _

/-- The operator norm of the full Jacobian bounds the norm of its
retained block. -/
theorem norm_sourcePsiSelectedRootJacobian_le_full
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (a : DeletedCoeff p n) (ψ : CoeffPair p) :
    ‖sourcePsiSelectedRootJacobian hp hp1 n c R a ψ‖ ≤
      ‖sourcePsiFullRootJacobian hp hp1 n c R a ψ‖ :=
  Coeff.norm_deletedOperator_le_norm_extension n 2 _

/-- At each canonical real gap-root solution there is a contour chart
whose full-space selected Jacobian is invertible. -/
theorem exists_sourcePsiFullRootJacobian_bijective_at_gapRoot
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : realTypeSourceLocus p) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      Function.Bijective
        (sourcePsiFullRootJacobian hp hp1 n c R
          (sourcePsiGapRoot hp hp1 n φ) φ.val) := by
  obtain ⟨c,R,s,hs,hsφ,hreal,hbij,hzero,hF,hderiv⟩ :=
    exists_sourcePsiGapRoot_derivative_equation hp hp1 n φ
  exact ⟨c,R,(sourcePsiFullRootJacobian_bijective_iff
    hp hp1 n c R (sourcePsiGapRoot hp hp1 n φ) φ.val).2 hbij⟩

end NLS.ZakharovShabat
