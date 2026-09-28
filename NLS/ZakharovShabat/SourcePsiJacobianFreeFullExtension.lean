import NLS.ZakharovShabat.SourcePsiJacobianFullExtension
import NLS.ZakharovShabat.SourcePsiFreeSequenceDerivative

/-!
# The full-space psi Jacobian at the free source

On free-centered contours, the selected sequence equation is exactly
the already formalized free psi equation. Its derivative is `2 · id`
on the deleted space. The block extension is `2 · id` on the common
full sequence space, independently of the deleted index. This is the
free-source base case of the limit operator in Lemma 12.10.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The selected sequence equation on uniform free-centered contours
is exactly the free-source sequence equation for every input. -/
theorem sourcePsiSelectedEquationSequence_free_eq
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (R : ℝ) (hR : 0 < R) (hRquarter : R ≤ Real.pi / 4)
    (a : DeletedCoeff p n) :
    sourcePsiSelectedEquationSequence hp hp1 n
      (fun m => (Real.pi : ℂ) * m) (fun _ => R) a 0 =
      sourcePsiFreeEquationSequence hp hp1 n R hR hRquarter a := by
  obtain ⟨F,hF⟩ :=
    exists_deletedCoeff_sourcePsiEquation_freeCircle_unconditional
      hp hp1 n a R hR hRquarter
  ext m
  rw [sourcePsiSelectedEquationSequence_apply_of_exists
    hp hp1 n (fun m => (Real.pi : ℂ) * m) (fun _ => R) a 0
      ⟨F,hF⟩ m]
  exact (sourcePsiFreeEquationSequence_apply
    hp hp1 n m R hR hRquarter a).symm

/-- The actual selected root Jacobian at free data is `2 · id`, for
every deleted index and every admissible uniform free-circle radius. -/
theorem sourcePsiSelectedRootJacobian_free_eq
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (R : ℝ) (hR : 0 < R) (hRquarter : R ≤ Real.pi / 4) :
    sourcePsiSelectedRootJacobian hp hp1 n
      (fun m => (Real.pi : ℂ) * m) (fun _ => R)
      0 0 = sourcePsiFreeJacobianOperator n := by
  have hfun : (fun a : DeletedCoeff p n =>
      sourcePsiSelectedEquationSequence hp hp1 n
        (fun m => (Real.pi : ℂ) * m) (fun _ => R) a 0) =
      sourcePsiFreeEquationSequence hp hp1 n R hR hRquarter := by
    funext a
    exact sourcePsiSelectedEquationSequence_free_eq
      hp hp1 n R hR hRquarter a
  change fderiv ℂ (fun a : DeletedCoeff p n =>
      sourcePsiSelectedEquationSequence hp hp1 n
        (fun m => (Real.pi : ℂ) * m) (fun _ => R) a 0) 0 = _
  rw [hfun]
  exact fderiv_sourcePsiFreeEquationSequence_zero
    hp hp1 n R hR hRquarter

/-- Every free selected Jacobian has the same full-space extension,
namely `2 · id` on `ℓᵖ(ℤ)`. -/
theorem sourcePsiFullRootJacobian_free_eq
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (R : ℝ) (hR : 0 < R) (hRquarter : R ≤ Real.pi / 4) :
    sourcePsiFullRootJacobian hp hp1 n
      (fun m => (Real.pi : ℂ) * m) (fun _ => R)
      0 0 = (2 : ℂ) • ContinuousLinearMap.id ℂ (Coeff p) := by
  rw [sourcePsiFullRootJacobian,
    sourcePsiSelectedRootJacobian_free_eq hp hp1 n R hR hRquarter]
  apply ContinuousLinearMap.ext
  intro a
  ext m
  by_cases hmn : m = n
  · subst m
    simp [Coeff.deletedJacobianExtension]
  · change (Coeff.deletedOperatorExtension n 2
      (sourcePsiFreeJacobianOperator n) a) m =
        ((2 : ℂ) • a) m
    rw [Coeff.deletedOperatorExtension_apply_other n m hmn,
      sourcePsiFreeJacobianOperator_apply]
    change (2 * (Coeff.deleteCoordinate n a) m) = 2 * a m
    rw [Coeff.deleteCoordinate_apply_other n m hmn]

/-- The same identity holds at the canonical real gap-root solution
over the free source. -/
theorem sourcePsiFullRootJacobian_free_gapRoot_eq
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (R : ℝ) (hR : 0 < R) (hRquarter : R ≤ Real.pi / 4) :
    sourcePsiFullRootJacobian hp hp1 n
      (fun m => (Real.pi : ℂ) * m) (fun _ => R)
      (sourcePsiGapRoot hp hp1 n
        (⟨0, by simp [realTypeSourceLocus]⟩ : realTypeSourceLocus p)) 0 =
      (2 : ℂ) • ContinuousLinearMap.id ℂ (Coeff p) := by
  rw [sourcePsiGapRoot_zero]
  exact sourcePsiFullRootJacobian_free_eq hp hp1 n R hR hRquarter

/-- At the free source, the full-space family already equals its
limit operator at every index, so its operator-norm error is zero. -/
theorem norm_sourcePsiFullRootJacobian_free_sub_limit
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (R : ℝ) (hR : 0 < R) (hRquarter : R ≤ Real.pi / 4) :
    ‖sourcePsiFullRootJacobian hp hp1 n
      (fun m => (Real.pi : ℂ) * m) (fun _ => R)
      0 0 - (2 : ℂ) • ContinuousLinearMap.id ℂ (Coeff p)‖ = 0 := by
  rw [sourcePsiFullRootJacobian_free_eq hp hp1 n R hR hRquarter]
  simp

end NLS.ZakharovShabat
