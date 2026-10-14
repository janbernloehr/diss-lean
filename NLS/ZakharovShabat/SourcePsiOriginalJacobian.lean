import NLS.ZakharovShabat.SourceLemma12_4
import NLS.SequenceSpaces.DeletedJacobianMatrixExpansion
import NLS.ComplexAnalysis.LocalRealAxisDerivative

/-!
# The actual root Jacobian on the original source domain

The derivative is taken in the deleted Banach space of the original
equation. Full root inputs specify all matrix entries at once, including
zero entries in the omitted row and column. Every original contour gives
the same scalar directional derivative. Reality follows directly from
the original equation, without restricting to a selected local chart.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The bounded root derivative of the original deleted equation. -/
def sourcePsiOriginalRootJacobian (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a : DeletedCoeff p n) (ψ : CoeffPair p) :
    DeletedCoeff p n →L[ℂ] DeletedCoeff p n :=
  fderiv ℂ (fun b => sourcePsiOriginalEquation hp hp1 n b ψ) a

/-- Matrix entries evaluated at the deletion of a full root input. -/
def sourcePsiOriginalJacobianEntry (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m r : ℤ) (a : Coeff p) (ψ : CoeffPair p) : ℂ :=
  Coeff.deletedOperatorMatrixEntry n
    (sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ) m r

@[simp] theorem sourcePsiOriginalJacobianEntry_deleted_column
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m : ℤ) (a : Coeff p) (ψ : CoeffPair p) :
    sourcePsiOriginalJacobianEntry hp hp1 n m n a ψ = 0 := by
  simp [sourcePsiOriginalJacobianEntry]

@[simp] theorem sourcePsiOriginalJacobianEntry_deleted_row
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n r : ℤ) (a : Coeff p) (ψ : CoeffPair p) :
    sourcePsiOriginalJacobianEntry hp hp1 n n r a ψ = 0 :=
  (sourcePsiOriginalRootJacobian hp hp1 n (Coeff.deleteCoordinateTo n a) ψ
    (Coeff.deleteCoordinateTo n (lp.single p r 1))).property

/-- The unused root fill does not change any actual matrix entry. -/
theorem sourcePsiOriginalJacobianEntry_add_single_deleted
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n m r : ℤ) (a : Coeff p) (ψ : CoeffPair p) (z : ℂ) :
    sourcePsiOriginalJacobianEntry hp hp1 n m r (a+lp.single p n z) ψ =
      sourcePsiOriginalJacobianEntry hp hp1 n m r a ψ := by
  simp only [sourcePsiOriginalJacobianEntry,map_add,Coeff.deleteCoordinateTo_single_same,add_zero]

theorem SourceLemma12_4Data.originalRootJacobian_hasFDerivAt
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n : ℤ) (a : DeletedCoeff p n) :
    HasFDerivAt (fun b => sourcePsiOriginalEquation hp hp1 n b ψ)
      (sourcePsiOriginalRootJacobian hp hp1 n a ψ) a := by
  exact ((H.analytic n (ψ,a) ⟨hψ,mem_univ _⟩).comp
    (f := fun b : DeletedCoeff p n => (ψ,b))
    (analyticAt_const.prod analyticAt_id)).differentiableAt.hasFDerivAt

/-- An actual matrix entry is the derivative along a full coordinate line. -/
theorem SourceLemma12_4Data.originalJacobianEntry_hasDerivAt
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n m r : ℤ) (a : Coeff p) :
    HasDerivAt (fun z : ℂ =>
      (sourcePsiOriginalEquation hp hp1 n
        (Coeff.deleteCoordinateTo n (a+lp.single p r z)) ψ : Coeff p) m)
      (sourcePsiOriginalJacobianEntry hp hp1 n m r a ψ) 0 := by
  let L : DeletedCoeff p n →L[ℂ] ℂ :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p m).comp
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).ker.subtypeL)
  have hF := H.originalRootJacobian_hasFDerivAt ψ hψ n (Coeff.deleteCoordinateTo n a)
  have hline : HasDerivAt (fun z : ℂ => a+lp.single p r z)
      (lp.single p r 1) 0 := by
    simpa using (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) p r).hasDerivAt.const_add a
  have hdel := (Coeff.deleteCoordinateTo (p := p) n).hasFDerivAt.comp_hasDerivAt
    (0 : ℂ) hline
  have hcomp := (L.hasFDerivAt.comp _ hF).comp_hasDerivAt_of_eq
    (0 : ℂ) hdel (by simp)
  exact hcomp

/-- The scalar contour equation agrees for every full root input. -/
theorem SourceLemma12_4Data.originalEquation_fullInput
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n m : ℤ) (a : Coeff p) (P : SourceCriticalRootPeriodCircle hp hp1 ψ m) :
    (sourcePsiOriginalEquation hp hp1 n (Coeff.deleteCoordinateTo n a) ψ : Coeff p) m =
      sourcePsiEquationCoordinate hp hp1 n m a ψ (P.center:ℂ) P.radius := by
  rw [sourcePsiEquationCoordinate_eq_deletedCoordinate hp hp1 n m a ψ
    (P.center:ℂ) P.radius P.radius_pos.le]
  exact H.equation ψ hψ n (Coeff.deleteCoordinateTo n a) m P

/-- Every original isolating circle computes the same matrix entry. -/
theorem SourceLemma12_4Data.originalJacobianEntry_eq_contour_deriv
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n m r : ℤ) (a : Coeff p) (P : SourceCriticalRootPeriodCircle hp hp1 ψ m) :
    sourcePsiOriginalJacobianEntry hp hp1 n m r a ψ =
      deriv (fun z : ℂ => sourcePsiEquationCoordinate hp hp1 n m
        (a+lp.single p r z) ψ (P.center:ℂ) P.radius) 0 := by
  have he : (fun z : ℂ =>
      (sourcePsiOriginalEquation hp hp1 n
        (Coeff.deleteCoordinateTo n (a+lp.single p r z)) ψ : Coeff p) m) =
      (fun z : ℂ => sourcePsiEquationCoordinate hp hp1 n m
        (a+lp.single p r z) ψ (P.center:ℂ) P.radius) :=
    funext (fun z => H.originalEquation_fullInput ψ hψ n m _ P)
  rw [← he]
  exact (H.originalJacobianEntry_hasDerivAt ψ hψ n m r a).deriv.symm

/-- All entries are real at real source and root data, on the entire W. -/
theorem SourceLemma12_4Data.originalJacobianEntry_real
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (hreal : IsRealType (CoeffPair.toMax p ψ)) (n m r : ℤ) (a : Coeff p)
    (ha : ∀ k : ℤ, (a k).im = 0) :
    (sourcePsiOriginalJacobianEntry hp hp1 n m r a ψ).im = 0 := by
  apply NLS.ComplexAnalysis.HasDerivAt.im_eq_zero_of_eventually_real _ _ 0
    (H.originalJacobianEntry_hasDerivAt ψ hψ n m r a)
  apply Filter.Eventually.of_forall
  intro y
  apply H.real ψ hψ hreal n _ _ m
  intro k
  by_cases hkn : k = n
  · subst k
    simp [Coeff.deleteCoordinateTo, Coeff.deleteCoordinate_apply_same]
  · change ((Coeff.deleteCoordinate n (a+lp.single p r (y:ℂ))) k).im = 0
    rw [Coeff.deleteCoordinate_apply_other n k hkn]
    by_cases hkr : k = r
    · subst k
      simp [ha]
    · simp [ha, hkr]

end NLS.ZakharovShabat
