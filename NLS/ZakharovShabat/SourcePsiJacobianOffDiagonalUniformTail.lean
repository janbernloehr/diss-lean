import NLS.ZakharovShabat.SourcePsiLimitMatrixOperator
import NLS.ZakharovShabat.SourcePsiJacobianDiagonalNormLimit
import NLS.SequenceSpaces.FullReciprocalMatrixTail

/-!
# Uniform high/high tails of the psi Jacobians

The fixed reciprocal-entry majorant for the common contour family
controls the off-diagonal high-output, high-input blocks in operator
norm. One pair of finite cutoffs works for the limit operator and every
sufficiently distant deleted-index Jacobian. The same contour family
also gives operator-norm convergence of their diagonal parts.
-/

noncomputable section
open Set Filter Topology Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Reciprocal tail-entry estimates on a prescribed contour family
give common high/high off-diagonal cutoffs for its full Jacobians and
limit operator. Deleted rows and columns contribute zero. -/
theorem sourcePsiFullRootJacobian_uniformOffDiagonalTail_of_reciprocalEntries
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : Coeff p) (φ : CoeffPair p) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (Qstar : Coeff p →L[ℂ] Coeff p) (Krow Kcol : ℕ) (b : Coeff p)
    (hoff : ∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
      ∀ m : ℤ, Krow ≤ m.natAbs → m ≠ n →
        ∀ k : ℤ, Kcol ≤ k.natAbs → k ≠ n → m ≠ k →
          ‖(sourcePsiFullRootJacobian hp hp1 n c R
            (Coeff.deleteCoordinateTo n a) φ (lp.single p k 1)) m‖ ≤
              ‖b m‖ / ‖((m-k : ℤ) : ℂ)‖)
    (hQoff : ∀ m k : ℤ, Krow ≤ m.natAbs → Kcol ≤ k.natAbs → m ≠ k →
      ‖(Qstar (lp.single p k 1)) m‖ ≤ ‖b m‖ / ‖((m-k : ℤ) : ℂ)‖) :
    ∀ ε : ℝ, 0 < ε → ∃ s t : Finset ℤ,
      (∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
        ‖(ContinuousLinearMap.id ℂ (Coeff p) - Coeff.truncateCLM s).comp
          ((Coeff.operatorOffDiagonal
            (sourcePsiFullRootJacobian hp hp1 n c R
              (Coeff.deleteCoordinateTo n a) φ)).comp
              (ContinuousLinearMap.id ℂ (Coeff p) - Coeff.truncateCLM t))‖ < ε) ∧
      ‖(ContinuousLinearMap.id ℂ (Coeff p) - Coeff.truncateCLM s).comp
        ((Coeff.operatorOffDiagonal Qstar).comp
          (ContinuousLinearMap.id ℂ (Coeff p) - Coeff.truncateCLM t))‖ < ε := by
  let : Fact (1 ≤ p.conjExponent) :=
    ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  have hden (m k : ℤ) :
      ‖((m-k : ℤ) : ℂ)‖ = |((k-m : ℤ) : ℝ)| := by
    rw [Complex.norm_intCast]
    simp only [Int.cast_sub,abs_sub_comm]
  intro ε hε
  obtain ⟨s,t,htail⟩ :=
    Coeff.exists_uniform_twoSidedTail_cutoffs_of_reciprocalEntries
      p.conjExponent hp b Krow Kcol ε hε
  refine ⟨s,t,?_,?_⟩
  · filter_upwards [hoff] with n hn
    apply htail
    intro m k hmr hkc hkm
    by_cases hmn : m = n
    · subst m
      rw [sourcePsiFullRootJacobian_entry_deleted_row hp hp1 n k hkm,norm_zero]
      exact div_nonneg (norm_nonneg (b n)) (abs_nonneg _)
    · by_cases hkn : k = n
      · subst k
        rw [sourcePsiFullRootJacobian_entry_deleted_column hp hp1 n m hmn,norm_zero]
        exact div_nonneg (norm_nonneg (b m)) (abs_nonneg _)
      · simpa only [hden] using hn m hmr hmn k hkc hkn hkm.symm
  · apply htail
    intro m k hmr hkc hkm
    simpa only [hden] using hQoff m k hmr hkc hkm.symm

/-- The bounded contour-limit operator and the escaping Jacobians
have uniformly small two-sided off-diagonal tails, and their diagonal
parts converge in operator norm. These are the diagonal and high/high
parts of the operator-norm argument in Lemma 12.10. -/
theorem exists_sourcePsiLimitMatrixOperator_uniformOffDiagonalTail
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
        sphere (c m) (R m) ⊆
          sourceCanonicalRootDomain hp hp1 φ) ∧
      ∃ Qstar : Coeff p →L[ℂ] Coeff p, ∃ M : ℝ,
        0 ≤ M ∧ ‖Qstar‖ ≤ M ∧
        (∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
          ‖sourcePsiFullRootJacobian hp hp1 n c R
            (Coeff.deleteCoordinateTo n a) φ‖ ≤ M) ∧
        (∀ x : Coeff p, ∀ m : ℤ,
          Tendsto (fun n : ℤ =>
            (sourcePsiFullRootJacobian hp hp1 n c R
              (Coeff.deleteCoordinateTo n a) φ x) m)
            (Filter.comap Int.natAbs Filter.atTop)
            (𝓝 ((Qstar x) m))) ∧
        (∀ m k : ℤ,
          (Qstar (lp.single p k 1)) m =
            sourcePsiLimitMatrixEntry hp hp1 m k a φ (c m) (R m)) ∧
        (∀ ε : ℝ, 0 < ε → ∃ s t : Finset ℤ,
          (∀ᶠ n : ℤ in Filter.comap Int.natAbs Filter.atTop,
            ‖(ContinuousLinearMap.id ℂ (Coeff p) - Coeff.truncateCLM s).comp
              ((Coeff.operatorOffDiagonal
                (sourcePsiFullRootJacobian hp hp1 n c R
                  (Coeff.deleteCoordinateTo n a) φ)).comp
                (ContinuousLinearMap.id ℂ (Coeff p) - Coeff.truncateCLM t))‖ < ε) ∧
          ‖(ContinuousLinearMap.id ℂ (Coeff p) - Coeff.truncateCLM s).comp
            ((Coeff.operatorOffDiagonal Qstar).comp
              (ContinuousLinearMap.id ℂ (Coeff p) - Coeff.truncateCLM t))‖ < ε) ∧
        Tendsto (fun n : ℤ => Coeff.multiplierCLM (p := p)
          (Coeff.operatorDiagonalSymbol
            (sourcePsiFullRootJacobian hp hp1 n c R
              (Coeff.deleteCoordinateTo n a) φ)))
          (Filter.comap Int.natAbs Filter.atTop)
          (𝓝 (Coeff.multiplierCLM (p := p) (Coeff.operatorDiagonalSymbol Qstar))) := by
  classical
  obtain ⟨c,R,hgeom,Qstar,M,hM,hQnorm,hbound,hpoint,hentry,
      Kfree,hfree,hmatrix,Krow,Kcol,b,hoff,hQoff⟩ :=
    exists_sourcePsiLimitMatrixOperator hp hp1 a φ hφ ha
  have hdiaglim := tendsto_sourcePsiFullRootJacobian_diagonal
    hp hp1 a φ hφ ha c R Kfree hfree hmatrix Qstar
    (fun m => hpoint (lp.single p m 1) m)
  refine ⟨c,R,hgeom,Qstar,M,hM,hQnorm,hbound,hpoint,hentry,?_,hdiaglim⟩
  exact sourcePsiFullRootJacobian_uniformOffDiagonalTail_of_reciprocalEntries
    hp hp1 a φ c R Qstar Krow Kcol b hoff hQoff

end NLS.ZakharovShabat
