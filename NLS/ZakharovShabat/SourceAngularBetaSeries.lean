import NLS.ZakharovShabat.SourceAngularBetaTheorem13_1
import NLS.SequenceSpaces.UniformHolderSums
import NLS.SequenceSpaces.CompactPuncturedKernel

/-!
# Absolute and locally uniform convergence of the actual beta series

The diagonal is omitted explicitly. The actual gap and Dirichlet-minus-
midpoint sequences supply the two Hölder majorants; a translated
punctured reciprocal lattice supplies the fixed conjugate multiplier.
No gap or terminal regularity assumption is needed.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ p.conjExponent) :=
  ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- The actual Dirichlet terminal displacement from the periodic midpoint. -/
def sourceDirichletMidpointDisplacement (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) : Coeff p :=
  sourceBoundaryDisplacement hp hp1 .dirichlet ψ - sourcePeriodicMidpointDisplacement hp hp1 ψ

@[simp] theorem sourceDirichletMidpointDisplacement_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (m : ℤ) :
    sourceDirichletMidpointDisplacement hp hp1 ψ m =
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m -
        sourceStandardRootMidpoint hp hp1 ψ m := by
  simp only [sourceDirichletMidpointDisplacement, lp.coeFn_sub, Pi.sub_apply,
    sourceBoundaryDisplacement_apply, sourcePeriodicMidpointDisplacement_apply,
    sourceStandardRootMidpoint]
  ring

/-- The summand in Section 13 with its diagonal explicitly omitted. -/
def sourceAngularBetaSeriesTerm (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) (m : ℤ) : ℂ := by
  classical
  exact if m = n then 0 else sourceAngularBeta hp hp1 n m s ψ

/-- Section 13's correction `βⁿ`, the sum of the actual off-diagonal terms. -/
def sourceAngularBetaCorrection (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p) : ℂ :=
  ∑' m : ℤ, sourceAngularBetaSeriesTerm hp hp1 n s ψ m

/-- The reciprocal estimate is exactly the Hölder bound with the
translated punctured lattice, including the zero diagonal. -/
theorem norm_sourceAngularBetaSeriesTerm_le_holder
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (C : ℝ) (hbeta : ∀ m : ℤ, m ≠ n →
      ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤ C *
        (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
          ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m -
            sourceStandardRootMidpoint hp hp1 ψ m‖) / |((n-m : ℤ) : ℝ)|)
    (m : ℤ) :
    ‖sourceAngularBetaSeriesTerm hp hp1 n s ψ m‖ ≤ C *
      (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
        ‖sourceDirichletMidpointDisplacement hp hp1 ψ m‖) *
      ‖Coeff.shift n (Coeff.puncturedLattice p.conjExponent
        ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)) m‖ := by
  classical
  rw [Coeff.norm_shift_puncturedLattice_apply]
  by_cases hmn : m = n
  · simp only [sourceAngularBetaSeriesTerm, if_pos hmn, norm_zero, mul_zero, le_refl]
  · rw [if_neg hmn, sourceDirichletMidpointDisplacement_apply]
    have habs : |((n-m : ℤ) : ℝ)| = |((m-n : ℤ) : ℝ)| := by
      push_cast
      exact abs_sub_comm _ _
    simpa only [sourceAngularBetaSeriesTerm, if_neg hmn, habs, div_eq_mul_inv] using hbeta m hmn

/-- Theorem 13.1(i) implies absolute convergence of every actual beta
correction, with a bound independent of the deleted index. -/
theorem summable_norm_sourceAngularBetaSeriesTerm_of_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (C : ℝ) (hC : 0 ≤ C) (hbeta : ∀ m : ℤ, m ≠ n →
      ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤ C *
        (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
          ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m -
            sourceStandardRootMidpoint hp hp1 ψ m‖) / |((n-m : ℤ) : ℝ)|) :
    Summable (fun m => ‖sourceAngularBetaSeriesTerm hp hp1 n s ψ m‖) ∧
      (∑' m, ‖sourceAngularBetaSeriesTerm hp hp1 n s ψ m‖) ≤
        C * (‖sourcePeriodicGapDisplacement hp hp1 ψ‖ +
          ‖sourceDirichletMidpointDisplacement hp hp1 ψ‖) *
        ‖Coeff.puncturedLattice p.conjExponent
          ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)‖ := by
  have hq : p.conjExponent ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  have hc := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  simpa only [Coeff.norm_shift] using Coeff.summable_norm_of_two_holder_bounds hc
    (sourcePeriodicGapDisplacement hp hp1 ψ) (sourceDirichletMidpointDisplacement hp hp1 ψ)
    (Coeff.shift n (Coeff.puncturedLattice p.conjExponent
      ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)))
    (sourceAngularBetaSeriesTerm hp hp1 n s ψ) C hC
    (norm_sourceAngularBetaSeriesTerm_le_holder hp hp1 n s ψ C hbeta)

/-- A uniform reciprocal estimate on an open source neighborhood
gives uniform convergence of symmetric beta sums on a smaller open
neighborhood, even at collapsed gaps and endpoint terminals. -/
theorem exists_local_uniform_sourceAngularBetaSeries_of_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k)
    (U : Set (CoeffPair p)) (hU : IsOpen U) (φ : CoeffPair p) (hφ : φ ∈ U)
    (hboundary : AnalyticAt ℂ (sourceBoundaryDisplacement hp hp1 .dirichlet) φ)
    (C : ℝ) (hC : 0 ≤ C) (hbeta : ∀ ψ ∈ U, ∀ n m : ℤ, m ≠ n →
      ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤ C *
        (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
          ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m -
            sourceStandardRootMidpoint hp hp1 ψ m‖) / |((n-m : ℤ) : ℝ)|) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ U ∧ ∀ n : ℤ,
      TendstoUniformlyOn
        (fun (N : ℕ) ψ => ∑ m ∈ Finset.Icc (-(N : ℤ)) N,
          sourceAngularBetaSeriesTerm hp hp1 n s ψ m)
        (sourceAngularBetaCorrection hp hp1 n s) atTop V := by
  obtain ⟨_,_,G,hG,hφG,Rg,hRg,hgap⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ (by norm_num : (0 : ℝ) < 1)
  obtain ⟨_,_,M,hM,hφM,Rm,hRm,hmid⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ (by norm_num : (0 : ℝ) < 1)
  have hnear : ∀ᶠ ψ in 𝓝 φ,
      ‖sourceBoundaryDisplacement hp hp1 .dirichlet ψ‖ <
        ‖sourceBoundaryDisplacement hp hp1 .dirichlet φ‖ + 1 :=
    hboundary.continuousAt.norm.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨B,hBsub,hB,hφB⟩ := _root_.mem_nhds_iff.mp hnear
  let V := ((U ∩ G) ∩ M) ∩ B
  refine ⟨V,((hU.inter hG).inter hM).inter hB,⟨⟨⟨hφ,hφG⟩,hφM⟩,hφB⟩,
    (fun ψ hψ => hψ.1.1.1),?_⟩
  intro n
  have hq : p.conjExponent ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  let b := Coeff.shift n (Coeff.puncturedLattice p.conjExponent
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top))
  have hcauchy := Coeff.uniformCauchySeqOn_two_holder_sums
    (sourcePeriodicGapDisplacement hp hp1) (sourceDirichletMidpointDisplacement hp hp1) b hq
    (sourceAngularBetaSeriesTerm hp hp1 n s) V C
    (Rg + (‖sourceBoundaryDisplacement hp hp1 .dirichlet φ‖ + 1) + Rm) hC
    (by
      intro ψ hψ
      have hg := (hgap ψ hψ.1.1.2).1
      have hm := (hmid ψ hψ.1.2).1
      have hb : ‖sourceBoundaryDisplacement hp hp1 .dirichlet ψ‖ ≤
          ‖sourceBoundaryDisplacement hp hp1 .dirichlet φ‖ + 1 :=
        (show _ < _ from hBsub hψ.2).le
      have hd : ‖sourceDirichletMidpointDisplacement hp hp1 ψ‖ ≤
          ‖sourceBoundaryDisplacement hp hp1 .dirichlet ψ‖ +
            ‖sourcePeriodicMidpointDisplacement hp hp1 ψ‖ := norm_sub_le _ _
      linarith)
    (fun ψ hψ => norm_sourceAngularBetaSeriesTerm_le_holder hp hp1 n s ψ C
      (hbeta ψ hψ.1.1.1 n))
  apply hcauchy.tendstoUniformlyOn_of_tendsto
  intro ψ hψ
  exact ((summable_norm_sourceAngularBetaSeriesTerm_of_bound hp hp1 n s ψ C hC
    (hbeta ψ hψ.1.1.1 n)).1.of_norm.hasSum).comp Finset.tendsto_Icc_neg

end NLS.ZakharovShabat
