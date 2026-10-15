import NLS.ZakharovShabat.SourceGapWeightedEtaOriginal
import NLS.ZakharovShabat.SourceStandardRootPairedJointDomain

/-!
# Original coordinates at complex collapsed gaps

At a collapsed gap both coordinates vanish exactly when the Dirichlet
root is the midpoint. Otherwise exactly one of the two signs is nonzero.
No potential realizing the latter condition is assumed or constructed here.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Section 15's locus where the Dirichlet root lies outside its periodic segment. -/
def sourceDirichletOutsideGap (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (n : ℤ) : Set (CoeffPair p) :=
  {ψ | ψ ∈ W ∧ canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n ∉ sourcePeriodicSegment hp hp1 ψ n}

/-- Real interlacing excludes every real source from the outside-gap locus. -/
theorem disjoint_sourceDirichletOutsideGap_realType (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (n : ℤ) :
    Disjoint (sourceDirichletOutsideGap hp hp1 W n) (realTypeSourceLocus p) := by
  apply Set.disjoint_left.mpr
  intro ψ hψ hreal
  exact hψ.2 (canonicalPeriodOneBoundaryRoots_mem_sourcePeriodicSegment_of_realType hp hp1 .dirichlet ψ hreal n)

/-- Analytic symmetric endpoints and Dirichlet roots make the outside-gap locus open. -/
theorem isOpen_sourceDirichletOutsideGap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (n : ℤ) (hW : IsOpen W)
    (hmid : AnalyticOnNhd ℂ (fun ψ : CoeffPair p => canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n) W)
    (hgap : AnalyticOnNhd ℂ (fun ψ : CoeffPair p => (canonicalPeriodicGap hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2) W)
    (hroot : AnalyticOnNhd ℂ (fun ψ : CoeffPair p =>
      canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) W) :
    IsOpen (sourceDirichletOutsideGap hp hp1 W n) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro φ ⟨hφ, havoidφ⟩
  obtain ⟨U, hU, hbase, havoid⟩ :=
    exists_joint_neighborhood_avoids_sourcePeriodicSegment hp hp1 φ
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet φ n) n
      (hmid φ hφ) (hgap φ hφ) havoidφ
  have hpair : ContinuousAt (fun ψ : CoeffPair p =>
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n, ψ)) φ :=
    (hroot φ hφ).continuousAt.prodMk continuousAt_id
  have hnear : ∀ᶠ ψ in 𝓝 φ,
      (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n, ψ) ∈ U :=
    hpair.eventually (hU.mem_nhds hbase)
  apply Filter.mem_of_superset (Filter.inter_mem (hW.mem_nhds hφ) hnear)
  intro ψ hψ
  exact ⟨hψ.1, havoid (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n, ψ) hψ.2⟩

namespace SourceLemma12_12Data
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The outside-gap locus is open in the full complex source space. -/
theorem dirichletOutsideGap_original_open (H : SourceLemma12_12Data hp hp1 W₀ W s) (n : ℤ) :
    IsOpen (sourceDirichletOutsideGap hp hp1 W n) :=
  isOpen_sourceDirichletOutsideGap hp hp1 W n H.original_theta_common_domain.source_open
    (fun ψ hψ => (H.original_theta_common_domain.symmetric_analytic ψ hψ n).1)
    (fun ψ hψ => (H.original_theta_common_domain.symmetric_analytic ψ hψ n).2)
    (H.original_theta_common_domain.roots_analytic .dirichlet n)

/-- The original open-gap phases converge to the analytic extension along any converging net. -/
theorem gapWeighted_original_phase_limit (H : SourceLemma12_12Data hp hp1 W₀ W s)
    {α : Type*} {l : Filter α} (u : α → CoeffPair p) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n : ℤ) (σ : ℂ) (hσ : σ = 1 ∨ σ = -1) (hu : Tendsto u l (𝓝 ψ))
    (hopen : ∀ᶠ j in l, u j ∈ W ∧
      canonicalPeriodicGap hp hp1 (periodOnePotential (u j)) (periodOnePotential_mem (u j)) n ≠ 0) :
    Tendsto (fun j => canonicalPeriodicGap hp hp1 (periodOnePotential (u j)) (periodOnePotential_mem (u j)) n *
      Complex.exp (σ*I*sourceAngularOriginalEta hp hp1 n s (u j))) l
        (𝓝 (sourceGapWeightedEtaCoordinate hp hp1 n s σ ψ)) := by
  apply ((H.gapWeightedEta_original_analytic n σ ψ hψ).continuousAt.tendsto.comp hu).congr'
  filter_upwards [hopen] with j hj
  exact H.gapWeightedEta_original_signed (u j) hj.1 n hj.2 σ hσ

/-- At a complex collapsed gap both coordinates vanish exactly when the terminal is the midpoint. -/
theorem gapWeighted_original_collapsed_pair_zero_iff (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0) :
    (sourceGapWeightedEtaCoordinate hp hp1 n s 1 ψ = 0 ∧
      sourceGapWeightedEtaCoordinate hp hp1 n s (-1) ψ = 0) ↔
        canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n = sourceStandardRootMidpoint hp hp1 ψ n := by
  let a := canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n-sourceStandardRootMidpoint hp hp1 ψ n
  let b := sourceDirichletEtaSineNumerator hp hp1 n ψ
  let R := sourceAngularEtaRemainder hp hp1 n s ψ
  have hplus : sourceGapWeightedEtaCoordinate hp hp1 n s 1 ψ = 0 ↔ a+I*b = 0 := by
    change -2*(a+1*I*b)*Complex.exp (1*I*R) = 0 ↔ _
    simp only [one_mul,mul_eq_zero,Complex.exp_ne_zero,or_false]
    norm_num
  have hminus : sourceGapWeightedEtaCoordinate hp hp1 n s (-1) ψ = 0 ↔ a-I*b = 0 := by
    change -2*(a+(-1)*I*b)*Complex.exp ((-1)*I*R) = 0 ↔ _
    simp only [neg_mul,one_mul,← sub_eq_add_neg]
    norm_num
  rw [hplus,hminus]
  constructor
  · rintro ⟨hp,hm⟩
    apply sub_eq_zero.mp
    change a = 0
    linear_combination (hp+hm)/2
  · intro he
    have ha : a = 0 := sub_eq_zero.mpr he
    obtain ⟨P,hμ⟩ := H.angular_original_circles ψ hψ
    have hid := sourceDirichletEtaSineNumerator_sq_add hp hp1 n ψ
      ((P n).closedBall_subset_omittedDomain (ball_subset_closedBall (hμ n)))
    change b^2+a^2 = _ at hid
    rw [ha,hgap] at hid
    have hb : b = 0 := by simpa using hid
    simp [ha,hb]

/-- Off the collapsed midpoint, exactly one signed coordinate is nonzero. -/
theorem gapWeighted_original_collapsed_pair_exactly_one_nonzero (H : SourceLemma12_12Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0)
    (hμτ : canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n ≠ sourceStandardRootMidpoint hp hp1 ψ n) :
    (sourceGapWeightedEtaCoordinate hp hp1 n s 1 ψ = 0 ∧
      sourceGapWeightedEtaCoordinate hp hp1 n s (-1) ψ ≠ 0) ∨
    (sourceGapWeightedEtaCoordinate hp hp1 n s 1 ψ ≠ 0 ∧
      sourceGapWeightedEtaCoordinate hp hp1 n s (-1) ψ = 0) := by
  have hn : ¬(sourceGapWeightedEtaCoordinate hp hp1 n s 1 ψ = 0 ∧
      sourceGapWeightedEtaCoordinate hp hp1 n s (-1) ψ = 0) :=
    fun h => hμτ ((gapWeighted_original_collapsed_pair_zero_iff H ψ hψ n hgap).mp h)
  obtain ⟨P,hμ⟩ := H.angular_original_circles ψ hψ
  have hprod := sourceGapWeightedEtaCoordinate_mul hp hp1 n s ψ
    ((P n).closedBall_subset_omittedDomain (ball_subset_closedBall (hμ n)))
  rw [hgap,zero_pow (by norm_num : (2:ℕ) ≠ 0)] at hprod
  rcases mul_eq_zero.mp hprod with ha | hb
  · exact Or.inl ⟨ha,fun hb => hn ⟨ha,hb⟩⟩
  · exact Or.inr ⟨fun ha => hn ⟨ha,hb⟩,hb⟩

end SourceLemma12_12Data
end NLS.ZakharovShabat
