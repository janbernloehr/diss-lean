import NLS.ZakharovShabat.SourceCriticalRootRatioProduct
import NLS.ZakharovShabat.SourceLemma10_10

/-!
# The critical-root quotient on the unchanged analytic domains

The actual spectral quotient and its literal product are jointly analytic
on the full moving-gap complement of the existing common source domain.
Restricting to the complement of the original closed disks gives exactly
the fixed product domain printed after equation (2.15). The selected
omitted factor is analytic through the selected gap on that same W.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- The actual spectral quotient is jointly analytic on the retained moving-gap domain. -/
theorem SourceLemma10_7Data.criticalRatioJoint (h : SourceLemma10_7Data hp hp1 W) :
    AnalyticOnNhd ℂ (sourceCriticalRootRatioJoint hp hp1)
      (sourceCanonicalRootJointDomain hp hp1 W) := by
  intro t ht
  exact (analyticOnNhd_sourceDiscriminantDerivative_joint hp hp1 t (mem_univ _)).div
    (h.joint.2 t ht) (h.nonzero t.2 t.1 ht.2)

/-- The literal full product is jointly analytic, including at zeros of individual numerator factors. -/
theorem SourceLemma10_7Data.criticalRatioLiteralJoint (h : SourceLemma10_7Data hp hp1 W) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => ∏' m : ℤ,
      (canonicalCriticalPoints hp hp1 (periodOnePotential t.2) (periodOnePotential_mem t.2) m-t.1)/
        sourceStandardRoot hp hp1 t.2 m t.1) (sourceCanonicalRootJointDomain hp hp1 W) := by
  intro t ht
  apply (analyticAt_const.mul (h.criticalRatioJoint t ht)).congr
  filter_upwards [h.joint.1.mem_nhds ht] with q hq
  exact (sourceCriticalRootRatio_hasProd hp hp1 q.2 q.1 hq.2).tprod_eq.symm

/-- Fixing the source gives analyticity on precisely the complement of all periodic gaps. -/
theorem SourceLemma10_7Data.criticalRatioSpectral (h : SourceLemma10_7Data hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) :
    AnalyticOnNhd ℂ (fun z => sourceCriticalRootRatioJoint hp hp1 (z,ψ))
      (⋃ m : ℤ, sourcePeriodicSegment hp hp1 ψ m)ᶜ := by
  rw [← sourceCanonicalRootDomain_eq_compl_iUnion]
  intro z hz
  exact (h.criticalRatioJoint (z,ψ) ⟨hψ,hz⟩).comp
    (f := fun z : ℂ => (z,ψ)) (analyticAt_id.prod analyticAt_const)

/-- The original fixed closed-disk complement embeds in the moving-gap domain. -/
theorem SourceIsolatingNeighborhoods.closedDiskComplement_subset_rootJoint
    {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (h : SourceIsolatingNeighborhoods hp hp1 V D c) (hVW : V ⊆ W) :
    (⋃ m : ℤ, closure (D m))ᶜ ×ˢ V ⊆ sourceCanonicalRootJointDomain hp hp1 W := by
  intro t ht
  refine ⟨hVW ht.2,?_⟩
  intro m hm
  exact ht.1 (mem_iUnion.mpr ⟨m,subset_closure (h.gap t.2 ht.2 m hm)⟩)

/-- The actual quotient retains the printed closed-disk domain, original V and original D. -/
theorem SourceLemma10_7Data.criticalRatioClosedFixed (h : SourceLemma10_7Data hp hp1 W)
    {V : Set (CoeffPair p)} (hVW : V ⊆ W) {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) :
    AnalyticOnNhd ℂ (sourceCriticalRootRatioJoint hp hp1) ((⋃ m : ℤ, closure (D m))ᶜ ×ˢ V) :=
  h.criticalRatioJoint.mono (hD.closedDiskComplement_subset_rootJoint hVW)

/-- The literal product has the same joint analyticity on the original fixed domain. -/
theorem SourceLemma10_7Data.criticalRatioLiteralClosedFixed (h : SourceLemma10_7Data hp hp1 W)
    {V : Set (CoeffPair p)} (hVW : V ⊆ W) {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => ∏' m : ℤ,
      (canonicalCriticalPoints hp hp1 (periodOnePotential t.2) (periodOnePotential_mem t.2) m-t.1)/
        sourceStandardRoot hp hp1 t.2 m t.1) ((⋃ m : ℤ, closure (D m))ᶜ ×ˢ V) :=
  h.criticalRatioLiteralJoint.mono (hD.closedDiskComplement_subset_rootJoint hVW)

/-- Removing a selected factor gives an analytic function on its omitted domain in the same W. -/
theorem SourceCorollary10_6Data.criticalRatioExtension (h : SourceCorollary10_6Data hp hp1 W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceCriticalRootRatioExtension hp hp1 n ψ)
      (sourceStandardRootOmittedDomain hp hp1 ψ n) := by
  intro z hz
  exact analyticAt_const.mul (h.spectral ψ hψ
    (canonicalCriticalDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)) n z hz)

end NLS.ZakharovShabat
