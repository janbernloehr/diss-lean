import NLS.ZakharovShabat.SourcePsiLimitMatrixOperator
import NLS.ZakharovShabat.SourcePsiJacobianEscapingDiagonalTail
import NLS.SequenceSpaces.OperatorDiagonalConvergence

/-!
# Operator-norm convergence of the diagonal psi Jacobians

The free-tail contour choices and retained-entry identities put the
scalar diagonal tail estimate on the common full-space Jacobian family.
The omitted diagonal is exactly two. Coordinatewise convergence to
`Q*` then gives convergence of the extracted diagonal operators in
operator norm, the `Dⁿ → D*` step of Lemma 12.10.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The diagonal correction of the common-contour full Jacobian is
uniformly small on distant output rows, eventually in the deleted
index. This includes the omitted diagonal, where the correction is zero. -/
theorem sourcePsiFullRootJacobian_diagonal_uniformTail
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ)
    (c : ℤ → ℂ) (R : ℤ → ℝ) (Kfree : ℕ)
    (hfree : ∀ m : ℤ, Kfree < m.natAbs →
      c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8)
    (hmatrix : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      ∀ m k : ℤ, ∀ _hmn : m ≠ n, ∀ hkn : k ≠ n,
        (sourcePsiFullRootJacobian hp hp1 n c R
          (Coeff.deleteCoordinateTo n a) φ (lp.single p k 1)) m =
          deriv (fun t : ℂ =>
            sourcePsiDeletedEquationCoordinate hp hp1 n m
              (Coeff.deleteCoordinateTo n a +
                Coeff.deletedSingleCLM n k hkn t) φ (c m) (R m)) 0) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℕ,
      ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        ∀ m : ℤ, K ≤ m.natAbs →
          ‖(sourcePsiFullRootJacobian hp hp1 n c R
            (Coeff.deleteCoordinateTo n a) φ (lp.single p m 1)) m-2‖ < ε := by
  intro ε hε
  obtain ⟨Kscalar,hscalar⟩ :=
    exists_sourcePsi_escaping_diagonal_scalarUniformTail hp hp1 a φ hφ ha ε hε
  refine ⟨max Kscalar (Kfree+1),?_⟩
  filter_upwards [hmatrix,hscalar] with n hn hs
  intro m hm
  by_cases hmn : m = n
  · subst m
    rw [sourcePsiFullRootJacobian_entry_deleted_diagonal]
    simpa using hε
  · have hmScalar : Kscalar ≤ m.natAbs := by omega
    have hmFree : Kfree < m.natAbs := by omega
    rw [hn m m hmn hmn,(hfree m hmFree).1,(hfree m hmFree).2]
    exact hs m hmScalar hmn

/-- The extracted diagonal operators of the full psi Jacobians
converge in norm to the diagonal of the coordinatewise limit operator. -/
theorem tendsto_sourcePsiFullRootJacobian_diagonal
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ)
    (c : ℤ → ℂ) (R : ℤ → ℝ) (Kfree : ℕ)
    (hfree : ∀ m : ℤ, Kfree < m.natAbs →
      c m = (Real.pi : ℂ)*m ∧ R m = Real.pi/8)
    (hmatrix : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      ∀ m k : ℤ, ∀ _hmn : m ≠ n, ∀ hkn : k ≠ n,
        (sourcePsiFullRootJacobian hp hp1 n c R
          (Coeff.deleteCoordinateTo n a) φ (lp.single p k 1)) m =
          deriv (fun t : ℂ =>
            sourcePsiDeletedEquationCoordinate hp hp1 n m
              (Coeff.deleteCoordinateTo n a +
                Coeff.deletedSingleCLM n k hkn t) φ (c m) (R m)) 0)
    (Qstar : Coeff p →L[ℂ] Coeff p)
    (hentry : ∀ m : ℤ,
      Tendsto (fun n : ℤ =>
        (sourcePsiFullRootJacobian hp hp1 n c R
          (Coeff.deleteCoordinateTo n a) φ (lp.single p m 1)) m)
        (Filter.comap Int.natAbs Filter.atTop)
        (𝓝 ((Qstar (lp.single p m 1)) m))) :
    Tendsto (fun n : ℤ => Coeff.multiplierCLM (p := p)
      (Coeff.operatorDiagonalSymbol
        (sourcePsiFullRootJacobian hp hp1 n c R
          (Coeff.deleteCoordinateTo n a) φ)))
      (Filter.comap Int.natAbs Filter.atTop)
      (𝓝 (Coeff.multiplierCLM (p := p) (Coeff.operatorDiagonalSymbol Qstar))) := by
  let : NeBot (Filter.comap Int.natAbs Filter.atTop) :=
    (inferInstance : NeBot (Filter.atTop : Filter ℕ)).comap_of_surj
      Int.natAbs_surjective
  exact Coeff.tendsto_operatorDiagonalMultiplier_of_uniform_constantTail
    (Filter.comap Int.natAbs Filter.atTop)
    (fun n => sourcePsiFullRootJacobian hp hp1 n c R
      (Coeff.deleteCoordinateTo n a) φ) Qstar 2 hentry
    (sourcePsiFullRootJacobian_diagonal_uniformTail
      hp hp1 a φ hφ ha c R Kfree hfree hmatrix)

end NLS.ZakharovShabat
