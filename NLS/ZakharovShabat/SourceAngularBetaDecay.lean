import NLS.ZakharovShabat.SourceAngularBetaSeries
import NLS.SequenceSpaces.ShiftedHolderDecay

/-!
# Vanishing of the actual beta correction

The two actual spectral displacement sequences lie in the finite
source exponent. The reciprocal lattice lies in its finite conjugate
exponent. Shifted Hölder decay therefore makes the complete absolute
sum of the actual off-diagonal beta terms tend to zero, and hence also
makes their complex correction tend to zero as `|n|` tends to infinity.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ p.conjExponent) :=
  ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- The all-index estimate of Theorem 13.1(i) makes both the complete
absolute beta sum and the actual correction vanish in both index
directions. Collapsed gaps and endpoint terminals remain included. -/
theorem sourceAngularBetaCorrection_decay_of_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) (ψ : CoeffPair p)
    (C : ℝ) (hC : 0 ≤ C) (hbeta : ∀ n m : ℤ, m ≠ n →
      ‖sourceAngularBeta hp hp1 n m s ψ‖ ≤ C *
        (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
          ‖canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ m -
            sourceStandardRootMidpoint hp hp1 ψ m‖) / |((n-m : ℤ) : ℝ)|) :
    Tendsto (fun n : ℤ => ∑' m : ℤ, ‖sourceAngularBetaSeriesTerm hp hp1 n s ψ m‖)
        cofinite (𝓝 0) ∧
      Tendsto (fun n : ℤ => sourceAngularBetaCorrection hp hp1 n s ψ) cofinite (𝓝 0) := by
  have hq : p.conjExponent ≠ ⊤ :=
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1).ne
  have hc := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  let b := Coeff.puncturedLattice p.conjExponent
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top)
  have hu (n m : ℤ) : ‖sourceAngularBetaSeriesTerm hp hp1 n s ψ m‖ ≤ C *
      (‖sourcePeriodicGapDisplacement hp hp1 ψ m‖ +
        ‖sourceDirichletMidpointDisplacement hp hp1 ψ m‖) * ‖Coeff.shift n b m‖ :=
    norm_sourceAngularBetaSeriesTerm_le_holder hp hp1 n s ψ C (hbeta n) m
  exact ⟨Coeff.tendsto_tsum_norm_of_two_shift_holder_bounds hp hq hc
      (sourcePeriodicGapDisplacement hp hp1 ψ) (sourceDirichletMidpointDisplacement hp hp1 ψ)
      b (fun n => sourceAngularBetaSeriesTerm hp hp1 n s ψ) C hC hu,
    Coeff.tendsto_tsum_of_two_shift_holder_bounds hp hq hc
      (sourcePeriodicGapDisplacement hp hp1 ψ) (sourceDirichletMidpointDisplacement hp hp1 ψ)
      b (fun n => sourceAngularBetaSeriesTerm hp hp1 n s ψ) C hC hu⟩

end NLS.ZakharovShabat
