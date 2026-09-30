import NLS.ZakharovShabat.SourcePsiGlobalHeadDiscBound
import NLS.ZakharovShabat.SourcePsiGapProductCompact
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Uniform quotient bounds on a disc near the full gap product

A fixed compact disc in the omitted-root domain has a local quotient
bound at each reference root vector. Compactness of the full gap
product selects finitely many such parameter neighborhoods and gives
a bound on one closed thickening of that entire product.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

theorem exists_sourcePsiQuotient_disc_bound_near_gapProduct
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p)
    (m : ℤ) (c : ℂ) (R : ℝ)
    (hdom : closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 φ.val m) :
    ∃ δ M : ℝ, 0 < δ ∧ 0 ≤ M ∧
      ∀ t ∈ cthickening δ (sourcePeriodicGapRootSet hp hp1 φ.val ×ˢ {φ.val}),
        ∀ z ∈ closedBall c R, ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,t)‖ ≤ M := by
  classical
  obtain ⟨W,_,_,hreal,hQ⟩ := exists_global_source_analytic_singleRootQuotient hp hp1
  let f := sourceSingleRootQuotientJointProduct hp hp1 m
  let D := sourceSingleRootQuotientJointDomain hp hp1 W m
  have hlocal (a : sourcePeriodicGapRootSet hp hp1 φ.val) :
      ∃ U : Set (Coeff p × CoeffPair p), IsOpen U ∧ (a.val,φ.val) ∈ U ∧
        ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ U, ∀ z ∈ closedBall c R, ‖f (z,t)‖ ≤ M := by
    obtain ⟨U,hU,hbase,M,hM,hbound⟩ :=
      NLS.ComplexAnalysis.exists_local_uniform_bound_on_compact_of_continuousOn
        f D (hQ m).1 (hQ m).2.continuousOn _ (isCompact_closedBall _ _)
        (a.val,φ.val) (fun z hz => ⟨hreal φ.property,hdom hz⟩)
    exact ⟨U,hU,hbase,M,hM,fun t ht z hz => (hbound t ht z hz).2⟩
  choose U hU hbase M hM hbound using hlocal
  let S := sourcePeriodicGapRootSet hp hp1 φ.val ×ˢ {φ.val}
  have hS : IsCompact S := (isCompact_sourcePeriodicGapRootSet hp hp1 φ.val).prod isCompact_singleton
  have hcover : S ⊆ ⋃ a : sourcePeriodicGapRootSet hp hp1 φ.val, U a := by
    rintro ⟨a,ψ⟩ ⟨ha,hψ⟩
    have heq : ψ = φ.val := mem_singleton_iff.mp hψ
    subst ψ
    exact mem_iUnion.mpr ⟨⟨a,ha⟩,hbase ⟨a,ha⟩⟩
  obtain ⟨s,hs⟩ := hS.elim_finite_subcover U hU hcover
  have hopen : IsOpen (⋃ a ∈ s, U a) := isOpen_biUnion (fun a _ => hU a)
  obtain ⟨δ,hδ,hthick⟩ := hS.exists_cthickening_subset_open hopen hs
  let C := ∑ a ∈ s, M a
  refine ⟨δ,C,hδ,Finset.sum_nonneg (fun a _ => hM a),?_⟩
  intro t ht z hz
  obtain ⟨a,ha⟩ := mem_iUnion.mp (hthick ht)
  obtain ⟨has,hta⟩ := mem_iUnion.mp ha
  exact (hbound a t hta z hz).trans (Finset.single_le_sum (fun b _ => hM b) has)

end NLS.ZakharovShabat
