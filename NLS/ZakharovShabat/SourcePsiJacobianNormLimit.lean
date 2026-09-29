import NLS.ZakharovShabat.SourcePsiJacobianColumnNormLimit
import NLS.ZakharovShabat.SourcePsiJacobianOffDiagonalUniformTail
import NLS.SequenceSpaces.OperatorNormFromProjections

/-!
# Operator-norm convergence of the full psi Jacobians

At a fixed gap-contained root vector and real-type potential, the
common-contour full Jacobians converge in operator norm to the bounded
contour-limit operator `Q*`. Finite input and output norm limits,
diagonal norm convergence, and common off-diagonal high/high cutoffs
are assembled on one contour family. This proves the fixed-root norm
limit used in Lemma 12.10; invertibility is a separate step.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- At every fixed gap-contained root vector, the full psi Jacobians
converge in operator norm as the deleted index escapes to infinity in
either direction. The limit has the prescribed contour matrix entries. -/
theorem exists_sourcePsiLimitMatrixOperator_normLimit
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ))
    (ha : a ∈ sourcePeriodicGapRootSet hp hp1 φ) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      (∀ m : ℤ,
        0 < R m ∧
        sourcePeriodicSegment hp hp1 φ m ⊆ ball (c m) (R m) ∧
        closedBall (c m) (R m) ⊆ sourceStandardRootOmittedDomain hp hp1 φ m ∧
        sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ) ∧
      ∃ Qstar : Coeff p →L[ℂ] Coeff p, ∃ M : ℝ,
        0 ≤ M ∧ ‖Qstar‖ ≤ M ∧
        (∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
          ‖sourcePsiFullRootJacobian hp hp1 n c R
            (Coeff.deleteCoordinateTo n a) φ‖ ≤ M) ∧
        (∀ m k : ℤ,
          (Qstar (lp.single p k 1)) m =
            sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m)) ∧
        Tendsto (fun n : ℤ => sourcePsiFullRootJacobian hp hp1 n c R
          (Coeff.deleteCoordinateTo n a) φ)
          (Filter.comap Int.natAbs Filter.atTop) (𝓝 Qstar) := by
  obtain ⟨c,R,hgeom,Qstar,M,hM,hQnorm,hbound,hpoint,hentry,
      Kfree,hfree,hmatrix,Krow,Kcol,b,hoff,hQoff⟩ :=
    exists_sourcePsiLimitMatrixOperator hp hp1 a φ hφ ha
  let l : Filter ℤ := Filter.comap Int.natAbs Filter.atTop
  let T (n : ℤ) : Coeff p →L[ℂ] Coeff p :=
    sourcePsiFullRootJacobian hp hp1 n c R (Coeff.deleteCoordinateTo n a) φ
  let : NeBot l :=
    (inferInstance : NeBot (Filter.atTop : Filter ℕ)).comap_of_surj
      Int.natAbs_surjective
  obtain ⟨K,bcol,hcolumns⟩ := sourcePsiFullRootJacobian_allColumn_tailMajorant
    hp hp1 a φ hφ c R (fun m => (hgeom m).2.2.2) Kfree hfree hmatrix
  have hcol (k : ℤ) : Tendsto (fun n => T n (lp.single p k 1))
      l (𝓝 (Qstar (lp.single p k 1))) := by
    apply Coeff.tendsto_operator_column_of_tailMajorant
      hp l T Qstar M hM hbound bcol K k
    · filter_upwards [hcolumns] with n hn
      intro m hm hmk
      exact hn m k hm hmk
    · exact hpoint (lp.single p k 1)
  have hinputTail := sourcePsiFullRootJacobian_finiteOutput_uniformInputTail
    hp hp1 a φ hφ c R (fun m => (hgeom m).1.le)
    (fun m => (hgeom m).2.2.1) (fun m => (hgeom m).2.2.2) hmatrix
  have houtput (s : Finset ℤ) :
      Tendsto (fun n => (Coeff.truncateCLM s).comp (T n)) l
        (𝓝 ((Coeff.truncateCLM s).comp Qstar)) :=
    Coeff.tendsto_finiteOutputs_of_coordinatewise_and_uniformInputTails T Qstar s
      hpoint (hinputTail s)
  have hinput := Coeff.tendsto_operator_finiteInputs_of_columns l T Qstar hcol
  have hdiag := tendsto_sourcePsiFullRootJacobian_diagonal
    hp hp1 a φ hφ ha c R Kfree hfree hmatrix Qstar
    (fun m => hpoint (lp.single p m 1) m)
  have htail := sourcePsiFullRootJacobian_uniformOffDiagonalTail_of_reciprocalEntries
    hp hp1 a φ c R Qstar Krow Kcol b hoff hQoff
  refine ⟨c,R,hgeom,Qstar,M,hM,hQnorm,hbound,hentry,?_⟩
  exact Coeff.tendsto_operator_of_finiteProjections_diagonal_and_offDiagonalTails
    l T Qstar houtput hinput hdiag htail

end NLS.ZakharovShabat
