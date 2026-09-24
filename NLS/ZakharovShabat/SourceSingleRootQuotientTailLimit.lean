import NLS.ZakharovShabat.SourceSingleRootUniformAsymptoticTailBounds
import NLS.ZakharovShabat.SourceGlobalIsolation

/-!
# Infinite quotient bounds on distant isolating discs

The finite Lemma 10.8 quotient estimates pass to the quotient product
once distant assigned discs are placed in the moving-gap complement.
Two local disc families may be used: sufficiently remote indices have
the same fixed free quarter-π disc in both families.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A distant point in one isolating-disc family also belongs to the
omitted-root domain supplied by a second disjoint isolating family. -/
theorem sourceSingleRootQuotientJointDomain_of_tail_isolation
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : CoeffPair p) (a : Coeff p)
    (Nbound Ngeom : ℕ) (εbound εgeom : ℝ)
    (hcluster : ∀ m : ℤ,
      sourceSpectralCluster hp hp1 ψ m ⊆
        sourceIsolatingDisc hp hp1 φ Ngeom εgeom m)
    (hdisjoint : ∀ i j : ℤ, i ≠ j →
      Disjoint (sourceIsolatingDisc hp hp1 φ Ngeom εgeom i)
        (sourceIsolatingDisc hp hp1 φ Ngeom εgeom j))
    (n : ℤ) (hnb : Nbound < n.natAbs) (hng : Ngeom < n.natAbs)
    (z : ℂ) (hz : z ∈ sourceIsolatingDisc hp hp1 φ Nbound εbound n) :
    (z,(a,ψ)) ∈ sourceSingleRootQuotientJointDomain hp hp1 Set.univ n := by
  have hzgeom : z ∈ sourceIsolatingDisc hp hp1 φ Ngeom εgeom n := by
    simpa only [sourceIsolatingDisc, if_neg (not_le.mpr hnb),
      if_neg (not_le.mpr hng)] using hz
  change ψ ∈ (Set.univ : Set (CoeffPair p)) ∧
    z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n
  refine ⟨Set.mem_univ _,?_⟩
  intro m hmn hmseg
  have hseg : sourcePeriodicSegment hp hp1 ψ m ⊆
      sourceIsolatingDisc hp hp1 φ Ngeom εgeom m :=
    sourcePeriodicSegment_subset_isolatingDisc hp hp1 φ ψ Ngeom εgeom m
      (hcluster m)
  exact Set.disjoint_left.mp (hdisjoint n m (Ne.symm hmn)) hzgeom
    (hseg hmseg)

/-- A bound valid for every finite cutoff passes to the literal
infinite quotient product at any point of its domain. -/
theorem norm_sourceSingleRootQuotientJointProduct_sub_one_le_of_partial
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (t : ℂ × (Coeff p × CoeffPair p))
    (ht : t ∈ sourceSingleRootQuotientJointDomain hp hp1 Set.univ n)
    (B : ℝ)
    (hB : ∀ M : ℕ,
      ‖sourceSingleRootQuotientPartialProduct hp hp1 n M t-1‖ ≤ B) :
    ‖sourceSingleRootQuotientJointProduct hp hp1 n t-1‖ ≤ B := by
  apply le_of_tendsto
    (((tendsto_sourceSingleRootQuotientPartialProduct hp hp1 n Set.univ t ht).sub_const 1).norm)
  exact Filter.Eventually.of_forall hB

/-- The finite large-index quotient bound passes to the analytic
infinite quotient product on one connected source neighborhood. -/
theorem exists_local_uniform_sourceSingleRootQuotientJointProduct_tail_bound
    {q : ℝ≥0∞} [Fact (1 ≤ q)]
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
              ∀ z ∈ sourceIsolatingDisc hp hp1 φ N ε n,
                ‖sourceSingleRootQuotientJointProduct hp hp1 n (z,(a,ψ))-1‖ ≤
                  Real.exp (C*‖α‖*‖Coeff.puncturedLattice q.conjExponent
                    ((ENNReal.HolderConjugate.lt_top_iff_one_lt q q.conjExponent).mp hq.lt_top)‖ +
                    (C^2/2)*∑' m : ℤ,
                      sourceSquaredGapReciprocalTerm hp hp1 ψ n m)-1 := by
  obtain ⟨N,ε,hε,hεmax,Vbound,hVboundOpen,_,hφVbound,C,hC,Kbound,hbound⟩ :=
    exists_local_uniform_sourceSingleRootQuotientPartialProduct_tail_bound
      hp hp1 hq φ hφ
  obtain ⟨Ngeom,εgeom,_,_,Vgeom,hVgeomOpen,_,hφVgeom,hcluster,hdisjoint⟩ :=
    exists_local_source_connected_isolating_discs hp hp1 φ hφ
  have hUopen : IsOpen (Vbound ∩ Vgeom) := hVboundOpen.inter hVgeomOpen
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp
    (hUopen.mem_nhds ⟨hφVbound,hφVgeom⟩)
  let K := max Kbound (max (N+1) (Ngeom+1))
  refine ⟨N,ε,hε,hεmax,ball φ r,Metric.isOpen_ball,
    isConnected_ball hr,mem_ball_self hr,C,hC,K,?_⟩
  intro ψ hψ n hn a α hα z hz
  have hψU : ψ ∈ Vbound ∩ Vgeom := hrU hψ
  have hKn : Kbound ≤ n.natAbs := by dsimp [K] at hn; omega
  have hNn : N < n.natAbs := by dsimp [K] at hn; omega
  have hNgeomn : Ngeom < n.natAbs := by dsimp [K] at hn; omega
  have hdomain : (z,(a,ψ)) ∈
      sourceSingleRootQuotientJointDomain hp hp1 Set.univ n :=
    sourceSingleRootQuotientJointDomain_of_tail_isolation
      hp hp1 φ ψ a N Ngeom ε εgeom
        (hcluster ψ hψU.2) hdisjoint n hNn hNgeomn z hz
  apply norm_sourceSingleRootQuotientJointProduct_sub_one_le_of_partial
    hp hp1 n (z,(a,ψ)) hdomain
  intro M
  exact hbound ψ hψU.1 n hKn a α hα M z hz

end NLS.ZakharovShabat
