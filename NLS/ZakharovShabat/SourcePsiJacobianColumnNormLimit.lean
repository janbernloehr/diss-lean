import NLS.ZakharovShabat.SourcePsiLimitMatrixOperator
import NLS.ZakharovShabat.SourcePsiJacobianAllColumnTail
import NLS.ZakharovShabat.SourcePsiJacobianFiniteRowTail
import NLS.SequenceSpaces.OperatorColumnConvergence

/-!
# Complete-column and finite-projection norm limits of the psi Jacobians

The common summable output bound upgrades the scalar contour limits
to norm convergence of full columns. Uniform boundedness extends this
to strong convergence on every input. Every fixed finite input block
also converges in operator norm and has uniformly small output tails.
The finite-row reciprocal bound gives the complementary high-input
cutoffs and finite-output operator-norm limits on the same contour
family, supplying both mixed-tail directions in Lemma 12.10.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- On the common contour family, the full psi Jacobians converge
strongly to the contour-limit operator. All fixed finite input
and finite output compressions converge in operator norm. Both
mixed-tail directions have eventual uniform cutoffs on this same
contour family. -/
theorem exists_sourcePsiLimitMatrixOperator_strong_and_finiteInputs
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      (∀ m : ℤ,
        0 < R m ∧
        sourcePeriodicSegment hp hp1 φ m ⊆ ball (c m) (R m) ∧
        closedBall (c m) (R m) ⊆
          sourceStandardRootOmittedDomain hp hp1 φ m ∧
        sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ) ∧
      ∃ Qstar : Coeff p →L[ℂ] Coeff p, ∃ M : ℝ,
        0 ≤ M ∧ ‖Qstar‖ ≤ M ∧
        (∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
          ‖sourcePsiFullRootJacobian hp hp1 n c R
            (Coeff.deleteCoordinateTo n a) φ‖ ≤ M) ∧
        (∀ m k : ℤ,
          (Qstar (lp.single p k 1)) m =
            sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m)) ∧
        (∀ x : Coeff p,
          Tendsto (fun n : ℤ => sourcePsiFullRootJacobian hp hp1 n c R
            (Coeff.deleteCoordinateTo n a) φ x)
            (Filter.comap Int.natAbs Filter.atTop) (𝓝 (Qstar x))) ∧
        (∀ s : Finset ℤ,
          Tendsto (fun n : ℤ =>
            (sourcePsiFullRootJacobian hp hp1 n c R
              (Coeff.deleteCoordinateTo n a) φ).comp (Coeff.truncateCLM s))
            (Filter.comap Int.natAbs Filter.atTop)
            (𝓝 (Qstar.comp (Coeff.truncateCLM s)))) ∧
        (∀ s : Finset ℤ,
          Tendsto (fun n : ℤ => (Coeff.truncateCLM s).comp
            (sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a) φ))
            (Filter.comap Int.natAbs Filter.atTop)
            (𝓝 ((Coeff.truncateCLM s).comp Qstar))) ∧
        (∀ s : Finset ℤ, ∀ ε : ℝ, 0 < ε → ∃ t : Finset ℤ,
          ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
            ‖(ContinuousLinearMap.id ℂ (Coeff p) - Coeff.truncateCLM t).comp
              ((sourcePsiFullRootJacobian hp hp1 n c R
                (Coeff.deleteCoordinateTo n a) φ).comp (Coeff.truncateCLM s))‖ < ε) ∧
        ∀ s : Finset ℤ, ∀ ε : ℝ, 0 < ε → ∃ t : Finset ℤ,
          ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
            ‖(Coeff.truncateCLM s).comp
              ((sourcePsiFullRootJacobian hp hp1 n c R
                (Coeff.deleteCoordinateTo n a) φ).comp
                (ContinuousLinearMap.id ℂ (Coeff p) - Coeff.truncateCLM t))‖ < ε := by
  obtain ⟨c,R,hgeom,Qstar,M,hM,hQnorm,hbound,hpoint,hentry,
      Kfree,hfree,hmatrix,_⟩ :=
    exists_sourcePsiLimitMatrixOperator hp hp1 a φ hφ ha
  let l : Filter ℤ := Filter.comap Int.natAbs Filter.atTop
  let T (n : ℤ) : Coeff p →L[ℂ] Coeff p :=
    sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a) φ
  let : NeBot l :=
    (inferInstance : NeBot (Filter.atTop : Filter ℕ)).comap_of_surj
      Int.natAbs_surjective
  obtain ⟨K,b,hcolumns⟩ := sourcePsiFullRootJacobian_allColumn_tailMajorant
    hp hp1 a φ hφ c R (fun m => (hgeom m).2.2.2) Kfree hfree hmatrix
  have hcol (k : ℤ) : Tendsto (fun n => T n (lp.single p k 1))
      l (𝓝 (Qstar (lp.single p k 1))) := by
    apply Coeff.tendsto_operator_column_of_tailMajorant
      hp l T Qstar M hM hbound b K k
    · filter_upwards [hcolumns] with n hn
      intro m hm hmk
      exact hn m k hm hmk
    · exact hpoint (lp.single p k 1)
  have hinput := sourcePsiFullRootJacobian_finiteOutput_uniformInputTail hp hp1 a φ hφ c R
    (fun m => (hgeom m).1.le) (fun m => (hgeom m).2.2.1)
    (fun m => (hgeom m).2.2.2) hmatrix
  refine ⟨c,R,hgeom,Qstar,M,hM,hQnorm,hbound,hentry,?_,?_,?_,?_,hinput⟩
  · exact Coeff.tendsto_operator_strong_of_columns hp l T Qstar M hM hQnorm hbound hcol
  · exact Coeff.tendsto_operator_finiteInputs_of_columns l T Qstar hcol
  · intro s
    exact Coeff.tendsto_finiteOutputs_of_coordinatewise_and_uniformInputTails T Qstar s
      hpoint (hinput s)
  · exact Coeff.exists_eventual_uniform_outputTail_of_finiteInputs hp l T Qstar hcol

end NLS.ZakharovShabat
