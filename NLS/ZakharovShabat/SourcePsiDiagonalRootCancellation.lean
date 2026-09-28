import NLS.ZakharovShabat.SourcePsiJacobianCollapsedDiagonal

/-!
# Independence of the omitted-root quotient from its deleted root

The product with index `m` deleted is insensitive to changes in the
`m`-th root coordinate. This remains true at root collisions, since
it follows from the literal finite products before passing to the
entire-product limit. The regular psi factor has the same property
when the deleted equation index differs from `m`.
-/

noncomputable section
open Filter
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Every finite deleted numerator cutoff is independent of the
omitted root coordinate. -/
theorem jointDeletedSingleSpectralPartialProduct_add_single_deleted
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (m : ℤ) (N : ℕ) (z : ℂ) (a : Coeff p) (t : ℂ) :
    jointDeletedSingleSpectralPartialProduct m N
      (z,a+lp.single p m t) =
    jointDeletedSingleSpectralPartialProduct m N (z,a) := by
  unfold jointDeletedSingleSpectralPartialProduct
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  have hkm : k ≠ m := (Finset.mem_erase.mp hk).1
  have hroot : displacedRoots (a+lp.single p m t) k =
      displacedRoots a k := by
    change (Real.pi : ℂ)*k + (a+lp.single p m t : Coeff p) k =
      (Real.pi : ℂ)*k + a k
    simp only [lp.coeFn_add,Pi.add_apply,
      lp.single_apply_ne _ _ _ hkm,add_zero]
  change singleSpectralFactor (displacedRoots (a+lp.single p m t)) z k =
    singleSpectralFactor (displacedRoots a) z k
  unfold singleSpectralFactor
  rw [hroot]

/-- The entire deleted numerator product is independent of the
omitted root coordinate, including at root collisions. -/
theorem jointDeletedSingleSpectralProduct_add_single_deleted
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (m : ℤ) (z : ℂ) (a : Coeff p) (t : ℂ) :
    jointDeletedSingleSpectralProduct m (z,a+lp.single p m t) =
    jointDeletedSingleSpectralProduct m (z,a) := by
  unfold jointDeletedSingleSpectralProduct
  congr 1
  funext N
  exact jointDeletedSingleSpectralPartialProduct_add_single_deleted
    m N z a t

/-- The omitted-root spectral quotient does not depend on the root
coordinate omitted from its numerator. -/
theorem sourceSingleRootQuotientJointProduct_add_single_deleted
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m : ℤ) (z : ℂ) (a : Coeff p) (ψ : CoeffPair p) (t : ℂ) :
    sourceSingleRootQuotientJointProduct hp hp1 m
      (z,(a+lp.single p m t,ψ)) =
    sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ)) := by
  unfold sourceSingleRootQuotientJointProduct
  rw [jointDeletedSingleSpectralProduct_add_single_deleted]

/-- Once the equation's deleted index is different, its regular gap
factor is also independent of the selected root coordinate. -/
theorem sourcePsiGapRegularFactor_add_single_selected
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n m : ℤ) (hnm : n ≠ m)
    (a : Coeff p) (ψ : CoeffPair p) (z t : ℂ) :
    sourcePsiGapRegularFactor hp hp1 n m
      (a+lp.single p m t) ψ z =
    sourcePsiGapRegularFactor hp hp1 n m a ψ z := by
  have hn : displacedRoots (a+lp.single p m t) n =
      displacedRoots a n := by
    change (Real.pi : ℂ)*n + (a+lp.single p m t : Coeff p) n =
      (Real.pi : ℂ)*n + a n
    simp only [lp.coeFn_add,Pi.add_apply,
      lp.single_apply_ne _ _ _ hnm,add_zero]
  unfold sourcePsiGapRegularFactor
  rw [sourceSingleRootQuotientJointProduct_add_single_deleted,hn]

end NLS.ZakharovShabat
