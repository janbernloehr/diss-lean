import NLS.ZakharovShabat.SourcePsiDeletedIndexAnalytic
import NLS.ZakharovShabat.SourcePsiOriginalJacobian

/-!
# The actual Jacobian on literal retained-index spaces

The root derivative is conjugate to the original bounded Jacobian by the
exact deleted-index isometry. This preserves both the operator norm and
every retained matrix entry on the full original source domain.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual root derivative on the literal retained-index lp spaces. -/
def sourcePsiDeletedIndexRootJacobian (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (ψ : CoeffPair p) (a : DeletedIndexCoeff p n) :
    DeletedIndexCoeff p n →L[ℂ] DeletedIndexCoeff p n :=
  fderiv ℂ (sourcePsiDeletedIndexEquation hp hp1 n ψ) a

theorem SourceLemma12_4Data.deletedIndexRootJacobian_hasFDerivAt
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n : ℤ) (a : DeletedIndexCoeff p n) :
    HasFDerivAt (sourcePsiDeletedIndexEquation hp hp1 n ψ)
      (sourcePsiDeletedIndexRootJacobian hp hp1 n ψ a) a :=
  ((H.deletedIndexEquation_analytic n (ψ,a) ⟨hψ,mem_univ _⟩).comp
    (f := fun b : DeletedIndexCoeff p n => (ψ,b))
    (analyticAt_const.prod analyticAt_id)).differentiableAt.hasFDerivAt

/-- Input zero extension and output restriction conjugate the original bounded derivative. -/
theorem SourceLemma12_4Data.deletedIndexRootJacobian_eq
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n : ℤ) (a : DeletedIndexCoeff p n) :
    sourcePsiDeletedIndexRootJacobian hp hp1 n ψ a =
      (DeletedCoeff.indexEquiv hp n).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((sourcePsiOriginalRootJacobian hp hp1 n ((DeletedCoeff.indexEquiv hp n).symm a) ψ).comp
          (DeletedCoeff.indexEquiv hp n).symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  let e := (DeletedCoeff.indexEquiv hp n).toContinuousLinearEquiv
  have ho := H.originalRootJacobian_hasFDerivAt ψ hψ n (e.symm a)
  have hc := e.hasFDerivAt.comp a (ho.comp a e.symm.hasFDerivAt)
  exact hc.fderiv

/-- The literal-index derivative has exactly the original operator norm. -/
theorem SourceLemma12_4Data.norm_deletedIndexRootJacobian
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n : ℤ) (a : DeletedIndexCoeff p n) :
    ‖sourcePsiDeletedIndexRootJacobian hp hp1 n ψ a‖ =
      ‖sourcePsiOriginalRootJacobian hp hp1 n ((DeletedCoeff.indexEquiv hp n).symm a) ψ‖ := by
  let e := DeletedCoeff.indexEquiv hp n
  let Q := sourcePsiOriginalRootJacobian hp hp1 n (e.symm a) ψ
  let T := sourcePsiDeletedIndexRootJacobian hp hp1 n ψ a
  have hT (b : DeletedIndexCoeff p n) : T b = e (Q (e.symm b)) := by
    rw [show T = _ from H.deletedIndexRootJacobian_eq ψ hψ n a]
    rfl
  apply le_antisymm
  · apply T.opNorm_le_bound (norm_nonneg Q)
    intro b
    rw [hT,e.norm_map]
    simpa only [e.symm.norm_map] using Q.le_opNorm (e.symm b)
  · apply Q.opNorm_le_bound (norm_nonneg T)
    intro b
    have h := T.le_opNorm (e b)
    simpa only [hT,e.symm_apply_apply,e.norm_map] using h

/-- Each retained matrix coefficient is unchanged by the exact index transport. -/
theorem SourceLemma12_4Data.deletedIndexRootJacobian_entry
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceLemma12_4Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n : ℤ) (a : DeletedIndexCoeff p n) (m r : {k : ℤ // k ≠ n}) :
    sourcePsiDeletedIndexRootJacobian hp hp1 n ψ a (lp.single p r 1) m =
      sourcePsiOriginalJacobianEntry hp hp1 n m.val r.val
        ((DeletedCoeff.indexEquiv hp n).symm a : Coeff p) ψ := by
  let e := DeletedCoeff.indexEquiv hp n
  have hsingle : e.symm (lp.single p r 1) =
      Coeff.deleteCoordinateTo n (lp.single p r.val 1) := by
    apply e.injective
    rw [e.apply_symm_apply]
    ext k
    change (lp.single p r 1 : DeletedIndexCoeff p n) k = (Coeff.deleteCoordinate n (lp.single p r.val 1)) k.val
    rw [Coeff.deleteCoordinate_apply_other n k.val k.property]
    simp only [lp.single_apply,Pi.single_apply,Subtype.ext_iff]
  have hproj : Coeff.deleteCoordinateTo n (e.symm a : Coeff p) = e.symm a := by
    apply Subtype.ext
    exact (Coeff.deleteCoordinate_eq_self_iff n _).2 (e.symm a).property
  rw [H.deletedIndexRootJacobian_eq ψ hψ n a]
  change (sourcePsiOriginalRootJacobian hp hp1 n (e.symm a) ψ
    (e.symm (lp.single p r 1)) : Coeff p) m.val = _
  rw [hsingle]
  unfold sourcePsiOriginalJacobianEntry Coeff.deletedOperatorMatrixEntry
  rw [hproj]

end NLS.ZakharovShabat
