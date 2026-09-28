import NLS.ZakharovShabat.SourcePsiLimitQuotient
import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Uniform deleted-coordinate limit of the single-root quotient

Joint continuity in a parameter and spectral variable becomes uniform
in the spectral variable on a compact set. Applied to Corollary 10.6,
this strengthens the pointwise quotient limit needed in Lemma 12.10 to
uniform convergence on every fixed valid contour disc.
-/

noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Continuity at one parameter and every point of a compact spectral
set gives uniform convergence as the parameter tends to that point. -/
theorem tendstoUniformlyOn_of_joint_continuousAt_compact
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PseudoMetricSpace Z]
    {K : Set Y} (hK : IsCompact K)
    {F : X → Y → Z} {a : X}
    (hF : ∀ y ∈ K,
      ContinuousAt (fun q : X × Y => F q.1 q.2) (a,y))
    {ι : Type*} {l : Filter ι} {a' : ι → X}
    (ha : Tendsto a' l (𝓝 a)) :
    TendstoUniformlyOn (fun i y => F (a' i) y) (F a) l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let S : Set (X × Y) :=
    {q | dist (F a q.2) (F q.1 q.2) < ε}
  have hS : S ∈ 𝓝 a ×ˢ 𝓝ˢ K := by
    apply hK.mem_prod_nhdsSet_of_forall
    intro y hy
    have hsection : ContinuousAt (F a) y :=
      (hF y hy).comp (continuousAt_const.prodMk continuousAt_id)
    have hbase : ContinuousAt (fun q : X × Y => F a q.2) (a,y) :=
      hsection.comp continuousAt_snd
    have hdist : ContinuousAt
        (fun q : X × Y => dist (F a q.2) (F q.1 q.2)) (a,y) :=
      hbase.dist (hF y hy)
    have hmem : S ∈ 𝓝 (a,y) := by
      exact hdist (Iio_mem_nhds (by simpa only [dist_self] using hε))
    simpa only [nhds_prod_eq] using hmem
  obtain ⟨U,hU,V,hV,hUV⟩ := Filter.mem_prod_iff.mp hS
  filter_upwards [ha.eventually hU] with i hi y hy
  have hpair : (a' i,y) ∈ U ×ˢ V :=
    ⟨hi,(subset_of_mem_nhdsSet hV) hy⟩
  exact hUV hpair

/-- The quotient with a deleted coordinate converges uniformly on a
fixed closed disc that avoids all standard-root gaps except the
retained row's gap. -/
theorem tendstoUniformlyOn_sourceSingleRootQuotient_deleteCoordinate
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m : ℤ) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (c : ℂ) (R : ℝ)
    (hdisc : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (a : Coeff p) :
    TendstoUniformlyOn
      (fun n : ℤ => fun z : ℂ =>
        sourceSingleRootQuotientJointProduct hp hp1 m
          (z,(Coeff.deleteCoordinate n a,ψ)))
      (fun z : ℂ =>
        sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ)))
      (Filter.comap Int.natAbs Filter.atTop) (closedBall c R) := by
  obtain ⟨W,_,_,hreal,hdata⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  apply tendstoUniformlyOn_of_joint_continuousAt_compact
    (isCompact_closedBall c R) (a := a)
    (a' := fun n : ℤ => Coeff.deleteCoordinate n a)
    (F := fun b : Coeff p => fun z : ℂ =>
      sourceSingleRootQuotientJointProduct hp hp1 m (z,(b,ψ)))
    ?_ (Coeff.tendsto_deleteCoordinate_at_natAbs hp a)
  intro z hz
  have ht : (z,(a,ψ)) ∈
      sourceSingleRootQuotientJointDomain hp hp1 W m :=
    ⟨hreal hψ,hdisc hz⟩
  have hAna := (hdata m).2 (z,(a,ψ)) ht
  have hinc : ContinuousAt
      (fun q : Coeff p × ℂ => (q.2,(q.1,ψ))) (a,z) := by fun_prop
  exact hAna.continuousAt.comp
    (f := fun q : Coeff p × ℂ => (q.2,(q.1,ψ))) hinc

/-- The quotient limit passes through a fixed valid circle integral.
The quotient is continuous on this contour for every deleted index. -/
theorem tendsto_circleIntegral_sourceSingleRootQuotient_deleteCoordinate
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (m : ℤ) (ψ : CoeffPair p)
    (hψ : IsRealType (CoeffPair.toMax p ψ))
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hdisc : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ m)
    (a : Coeff p) :
    Tendsto (fun n : ℤ =>
      ∮ z in C(c,R),
        sourceSingleRootQuotientJointProduct hp hp1 m
          (z,(Coeff.deleteCoordinate n a,ψ)))
      (Filter.comap Int.natAbs Filter.atTop)
      (𝓝 (∮ z in C(c,R),
        sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ)))) := by
  obtain ⟨W,_,_,hreal,hdata⟩ :=
    exists_global_source_analytic_singleRootQuotient hp hp1
  have hcont : ∀ n : ℤ,
      ContinuousOn
        (fun z : ℂ => sourceSingleRootQuotientJointProduct hp hp1 m
          (z,(Coeff.deleteCoordinate n a,ψ))) (sphere c R) := by
    intro n z hz
    have hzdisc : z ∈ closedBall c R := sphere_subset_closedBall hz
    have ht : (z,(Coeff.deleteCoordinate n a,ψ)) ∈
        sourceSingleRootQuotientJointDomain hp hp1 W m :=
      ⟨hreal hψ,hdisc hzdisc⟩
    have hAna := (hdata m).2 (z,(Coeff.deleteCoordinate n a,ψ)) ht
    have hinc : ContinuousAt
        (fun w : ℂ => (w,(Coeff.deleteCoordinate n a,ψ))) z := by fun_prop
    exact (hAna.continuousAt.comp
      (f := fun w : ℂ => (w,(Coeff.deleteCoordinate n a,ψ))) hinc).continuousWithinAt
  exact ((tendstoUniformlyOn_sourceSingleRootQuotient_deleteCoordinate
    hp hp1 m ψ hψ c R hdisc a).mono
      sphere_subset_closedBall).tendsto_circleIntegral_of_continuousOn
        hR (Filter.Eventually.of_forall hcont)

end NLS.ZakharovShabat
