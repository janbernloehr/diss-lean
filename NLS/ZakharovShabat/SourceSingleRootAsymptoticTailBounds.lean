import NLS.ZakharovShabat.SourceSingleRootMidpointBounds
import NLS.ZakharovShabat.SourceSquaredGapRowTails

/-!
# Large-index finite quotient bounds for Lemma 10.8

At each fixed source, the squared-gap row tends to zero at both ends
of the lattice. Its eventual half-unit bound activates the finite
midpoint-plus-gap product estimate simultaneously for every cutoff,
spectral point in the corresponding isolating disc, and root sequence
with an `ℓᑫ` root-minus-midpoint displacement.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- For a fixed source and separation constant, one threshold makes
the full finite quotient estimate valid on all sufficiently remote
isolating discs. The threshold does not depend on the numerator roots. -/
theorem exists_sourceSingleRootQuotientPartialProduct_tail_bound
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤)
    (φ ψ : CoeffPair p) (N : ℕ) (ε C : ℝ) (hC : 1 ≤ C)
    (hsep : ∀ i j : ℤ, i ≠ j →
      ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε i,
        |((i-j : ℤ) : ℝ)| ≤ C *
          ‖canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
            (periodOnePotential_mem ψ) j-z‖) :
    ∃ K : ℕ, ∀ n : ℤ, K ≤ n.natAbs →
      ∀ a : Coeff p, ∀ α : Coeff q,
        (∀ m : ℤ,
          displacedRoots a m -
            canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
              (periodOnePotential_mem ψ) m = α m) →
        ∀ M : ℕ, ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε n,
          ‖sourceSingleRootQuotientPartialProduct hp hp1 n M (z,(a,ψ))-1‖ ≤
            Real.exp (C*‖α‖*‖Coeff.puncturedLattice q.conjExponent
              ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖ +
              (C^2/2)*∑' m : ℤ,
                sourceSquaredGapReciprocalTerm hp hp1 ψ n m)-1 := by
  obtain ⟨K,hK⟩ := exists_sourceSquaredGapPhysicalRows_half_unit hp hp1 ψ C hC
  refine ⟨K,?_⟩
  intro n hn a α hα M z hz
  exact norm_sourceSingleRootQuotientPartialProduct_sub_one_le_of_small_row
    hp hp1 hq φ ψ a α hα N ε C hC hsep n M z hz (hK n hn)

/-- Near each real-type source, one connected neighborhood and one
separation constant work for every source in the neighborhood. The
large-index threshold here is allowed to depend on that source. -/
theorem exists_local_sourceSingleRootQuotientPartialProduct_tail_bound
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∃ C : ℝ, 1 ≤ C ∧
          ∀ ψ ∈ V, ∃ K : ℕ, ∀ n : ℤ, K ≤ n.natAbs →
            ∀ a : Coeff p, ∀ α : Coeff q,
              (∀ m : ℤ,
                displacedRoots a m -
                  canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ)
                    (periodOnePotential_mem ψ) m = α m) →
              ∀ M : ℕ, ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε n,
                ‖sourceSingleRootQuotientPartialProduct hp hp1 n M (z,(a,ψ))-1‖ ≤
                  Real.exp (C*‖α‖*‖Coeff.puncturedLattice q.conjExponent
                    ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖ +
                    (C^2/2)*∑' m : ℤ,
                      sourceSquaredGapReciprocalTerm hp hp1 ψ n m)-1 := by
  obtain ⟨N,ε,hε,hεmax,V,hVopen,hVconn,hφV,C,hC,hsep⟩ :=
    exists_local_source_midpoint_index_separation hp hp1 φ hφ
  refine ⟨N,ε,hε,hεmax,V,hVopen,hVconn,hφV,C,hC,?_⟩
  intro ψ hψ
  exact exists_sourceSingleRootQuotientPartialProduct_tail_bound
    hp hp1 hq φ ψ N ε C hC (hsep ψ hψ)

end NLS.ZakharovShabat
