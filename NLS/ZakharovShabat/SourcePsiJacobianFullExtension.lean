import NLS.SequenceSpaces.UniformInverseBound
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

/-- Quantitative inverse bound for the selected psi Jacobian. Once
the full-space extensions are shown to approach an invertible limit,
this bound supplies the tail-uniform inverse estimate in Lemma 12.10. -/
theorem norm_sourcePsiSelectedRootJacobian_inverse_le_of_full_near
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (c : ℤ → ℂ) (R : ℤ → ℝ)
    (a : DeletedCoeff p n) (ψ : CoeffPair p)
    (hbij : Function.Bijective
      (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ))
    (S R₀ : Coeff p →L[ℂ] Coeff p)
    (hR₀S : R₀.comp S = ContinuousLinearMap.id ℂ (Coeff p))
    (hnear : ‖R₀‖ * ‖S - sourcePsiFullRootJacobian hp hp1 n c R a ψ‖ ≤
      (1 / 2 : ℝ)) :
    ‖(ContinuousLinearEquiv.ofBijective
        (sourcePsiSelectedRootJacobian hp hp1 n c R a ψ)
        (LinearMap.ker_eq_bot.mpr hbij.1)
        (LinearMap.range_eq_top.mpr hbij.2)).symm.toContinuousLinearMap‖ ≤
      2 * ‖R₀‖ := by
  let Q := sourcePsiSelectedRootJacobian hp hp1 n c R a ψ
  let e := ContinuousLinearEquiv.ofBijective Q
    (LinearMap.ker_eq_bot.mpr hbij.1)
    (LinearMap.range_eq_top.mpr hbij.2)
  have hQR : Q.comp e.symm.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ (DeletedCoeff p n) := by
    apply ContinuousLinearMap.ext
    intro x
    change e (e.symm x) = x
    exact e.apply_symm_apply x
  exact Coeff.norm_deleted_inverse_le_two_mul_of_extension_near
    n Q e.symm.toContinuousLinearMap S R₀ hQR hR₀S hnear

/-- For a family of valid contour charts at the canonical real gap
roots, operator-norm convergence of the extended Jacobians to a
single invertible operator bounds all deleted inverse Jacobians.
The convergence premise is the remaining analytic estimate in the
first stage of Lemma 12.10. -/
theorem exists_uniform_sourcePsiGapRoot_inverse_norm_of_full_converges
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceLocus p)
    (c : ℤ → ℤ → ℂ) (r : ℤ → ℤ → ℝ)
    (hbij : ∀ n : ℤ, Function.Bijective
      (sourcePsiSelectedRootJacobian hp hp1 n (c n) (r n)
        (sourcePsiGapRoot hp hp1 n φ) φ.val))
    (S R₀ : Coeff p →L[ℂ] Coeff p)
    (hR₀S : R₀.comp S = ContinuousLinearMap.id ℂ (Coeff p))
    (hconv : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ n : ℤ,
      K ≤ n.natAbs →
        ‖S - sourcePsiFullRootJacobian hp hp1 n (c n) (r n)
          (sourcePsiGapRoot hp hp1 n φ) φ.val‖ < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ n : ℤ,
      ‖(ContinuousLinearEquiv.ofBijective
        (sourcePsiSelectedRootJacobian hp hp1 n (c n) (r n)
          (sourcePsiGapRoot hp hp1 n φ) φ.val)
        (LinearMap.ker_eq_bot.mpr (hbij n).1)
        (LinearMap.range_eq_top.mpr (hbij n).2)).symm.toContinuousLinearMap‖ ≤ M := by
  let Q : (n : ℤ) → DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
    fun n => sourcePsiSelectedRootJacobian hp hp1 n (c n) (r n)
      (sourcePsiGapRoot hp hp1 n φ) φ.val
  let e : (n : ℤ) → DeletedCoeff p n ≃L[ℂ] DeletedCoeff p n :=
    fun n => ContinuousLinearEquiv.ofBijective (Q n)
      (LinearMap.ker_eq_bot.mpr (hbij n).1)
      (LinearMap.range_eq_top.mpr (hbij n).2)
  let invQ : (n : ℤ) → DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
    fun n => (e n).symm.toContinuousLinearMap
  have hQR : ∀ n, (Q n).comp (invQ n) =
      ContinuousLinearMap.id ℂ (DeletedCoeff p n) := by
    intro n
    apply ContinuousLinearMap.ext
    intro x
    change (e n) ((e n).symm x) = x
    exact (e n).apply_symm_apply x
  have hconvQ : ∀ ε : ℝ, 0 < ε → ∃ K : ℕ, ∀ n : ℤ,
      K ≤ n.natAbs → ‖S - Coeff.deletedJacobianExtension n (Q n)‖ < ε := by
    simpa only [Q,sourcePsiFullRootJacobian] using hconv
  exact Coeff.exists_uniform_norm_deleted_inverse_of_extension_converges
    Q invQ S R₀ hQR hR₀S hconvQ

end NLS.ZakharovShabat
