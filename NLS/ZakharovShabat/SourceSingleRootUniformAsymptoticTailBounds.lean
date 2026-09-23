import NLS.ZakharovShabat.SourceSingleRootAsymptoticTailBounds
import NLS.ZakharovShabat.SourceSquaredGapUniformRowTails

/-!
# Locally uniform large-index finite quotient bounds

The midpoint separation constant and the squared-gap half-unit row
threshold can be chosen together on a connected source neighborhood.
Thus the finite Lemma 10.8 quotient bound holds on every sufficiently
remote isolating disc with a threshold independent of the nearby source,
the numerator roots, the cutoff, and the spectral point.
-/

noncomputable section
open Set Metric Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A single connected source neighborhood and large-index threshold
activate the finite full-quotient bound uniformly in all parameters
except the expected displacement norm and squared-gap row. -/
theorem exists_local_uniform_sourceSingleRootQuotientPartialProduct_tail_bound
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ N : ℕ, ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.pi/4 ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ IsConnected V ∧ φ ∈ V ∧
        ∃ C : ℝ, 1 ≤ C ∧ ∃ K : ℕ,
          ∀ ψ ∈ V, ∀ n : ℤ, K ≤ n.natAbs →
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
  obtain ⟨N,ε,hε,hεmax,Vsep,hVsepOpen,hVsepConn,hφVsep,C,hC,hsep⟩ :=
    exists_local_source_midpoint_index_separation hp hp1 φ hφ
  obtain ⟨Vrow,hVrowOpen,hφVrow,K,hrow⟩ :=
    exists_uniform_sourceSquaredGapPhysicalRows_half_unit hp hp1 φ C hC
  let U := Vsep ∩ Vrow
  have hUopen : IsOpen U := hVsepOpen.inter hVrowOpen
  have hφU : φ ∈ U := ⟨hφVsep,hφVrow⟩
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hφU)
  refine ⟨N,ε,hε,hεmax,ball φ r,Metric.isOpen_ball,
    isConnected_ball hr,mem_ball_self hr,C,hC,K,?_⟩
  intro ψ hψ n hn a α hα M z hz
  have hψU : ψ ∈ U := hrU hψ
  exact norm_sourceSingleRootQuotientPartialProduct_sub_one_le_of_small_row
    hp hp1 hq φ ψ a α hα N ε C hC (hsep ψ hψU.1) n M z hz
      (hrow ψ hψU.2 n hn)

end NLS.ZakharovShabat
