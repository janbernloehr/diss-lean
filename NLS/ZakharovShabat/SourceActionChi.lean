import NLS.ZakharovShabat.SourceCriticalDisplacementCommonAnalytic
import NLS.ZakharovShabat.SourceCriticalRootRatioCommonDomain
import NLS.ZakharovShabat.SourceNormalizedActionFree

/-!
# The literal deleted product χ_n in equation (2.18)

The actual critical displacement can be substituted into Corollary 10.6
on the unchanged source domain. The resulting literal product is jointly
analytic wherever the other gap segments are absent, including throughout
the selected original disk. No selected critical factor is divided out.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The product printed in (2.18), with precisely the index n omitted. -/
def sourceActionChi (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  ∏' m : {m : ℤ // m ≠ n},
    (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z) /
      sourceStandardRoot hp hp1 ψ m z

/-- The deleted free product is one, including at the selected collapsed gap. -/
theorem sourceActionChi_zero_source (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 (0 : CoeffPair p) n) :
    sourceActionChi hp hp1 n (0 : CoeffPair p) z = 1 := by
  have hf (m : {m : ℤ // m ≠ n}) :
      (canonicalCriticalPoints hp hp1 (periodOnePotential (0 : CoeffPair p))
        (periodOnePotential_mem (0 : CoeffPair p)) m-z) /
          sourceStandardRoot hp hp1 (0 : CoeffPair p) m z = 1 := by
    have hne := sourceStandardRoot_ne_zero_off_segment hp hp1 0 m z (hz m m.property)
    simp only [sourceStandardRoot_zero_source] at hne
    simpa only [map_zero,canonicalCriticalPoints_zero,sourceStandardRoot_zero_source] using div_self hne
  simp only [sourceActionChi,hf,tprod_one]

/-- The unordered literal product equals the existing analytic quotient. -/
theorem sourceActionChi_eq_quotient (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sourceActionChi hp hp1 n ψ z = sourceSingleRootQuotientJointProduct hp hp1 n
      (z,(sourceCriticalDisplacement hp hp1 ψ,ψ)) := by
  simpa only [sourceActionChi,sourceCriticalDisplacement,displacedRoots_canonicalCriticalDisplacement] using
    (hasProd_sourceSingleRootQuotient_subtype hp hp1 ψ
      (sourceCriticalDisplacement hp hp1 ψ) z n hz).tprod_eq

/-- The earlier deleted extension includes the factor -i; χ_n does not. -/
theorem sourceCriticalRootRatioExtension_eq_neg_I_chi (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (z : ℂ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sourceCriticalRootRatioExtension hp hp1 n ψ z = -Complex.I*sourceActionChi hp hp1 n ψ z := by
  rw [sourceActionChi_eq_quotient hp hp1 ψ n z hz]
  rfl

/-- Equation (2.18) with its exact -i normalization and literal deleted product. -/
theorem sourceCriticalRootRatio_eq_selectedFactor_mul_chi (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 ψ) :
    deriv (canonicalDiscriminant hp (periodOnePotential ψ)) z / sourceCanonicalRoot hp hp1 ψ z =
      -Complex.I*((canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n-z)/sourceStandardRoot hp hp1 ψ n z)*
          sourceActionChi hp hp1 n ψ z := by
  rw [sourceCriticalRootRatio_eq_selectedFactor_mul_extension hp hp1 ψ n z hz,
    sourceCriticalRootRatioExtension_eq_neg_I_chi hp hp1 ψ n z (fun m _ => hz m)]
  ring

/-- Joint analyticity holds on the entire omitted moving-gap domain of the same W. -/
theorem SourceCorollary10_6Data.chi_joint
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W) (hW : IsOpen W) (n : ℤ) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => sourceActionChi hp hp1 n t.2 t.1)
      (sourceStandardRootOmittedJointDomain hp hp1 W n) := by
  have ha := H.roots.roots.symmetric.simplicity.criticalDisplacement_analytic hW
  intro t ht
  have hmap : AnalyticAt ℂ (fun q : ℂ × CoeffPair p =>
      (q.1,(sourceCriticalDisplacement hp hp1 q.2,q.2))) t :=
    analyticAt_fst.prod (((ha t.2 ht.1).comp analyticAt_snd).prod analyticAt_snd)
  have hquot := ((H.joint n).2 (t.1,(sourceCriticalDisplacement hp hp1 t.2,t.2)) ht).comp
    (f := fun q : ℂ × CoeffPair p => (q.1,(sourceCriticalDisplacement hp hp1 q.2,q.2))) hmap
  apply hquot.congr
  filter_upwards [(H.roots.joint n).1.mem_nhds ht] with q hq
  exact (sourceActionChi_eq_quotient hp hp1 q.2 n q.1 hq.2).symm

/-- The fixed-domain assertion uses the other original closed disks, indexed by m. -/
theorem SourceCorollary10_6Data.chi_fixed
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W) (hW : IsOpen W) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (n : ℤ) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => sourceActionChi hp hp1 n t.2 t.1)
      ((⋃ m : ℤ, ⋃ (_ : m ≠ n), closure (D m))ᶜ ×ˢ V) := by
  apply (H.chi_joint hW n).mono
  intro t ht
  refine ⟨hVW ht.2,?_⟩
  intro m hmn hgap
  exact ht.1 (mem_iUnion.mpr ⟨m,mem_iUnion.mpr ⟨hmn,subset_closure (hD.gap t.2 ht.2 m hgap)⟩⟩)

/-- In particular χ_n is analytic through the entire selected original disk. -/
theorem SourceCorollary10_6Data.chi_disk
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceCorollary10_6Data hp hp1 W) (hW : IsOpen W) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (n : ℤ) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p => sourceActionChi hp hp1 n t.2 t.1) (D n ×ˢ V) :=
  (H.chi_joint hW n).mono (fun t ht =>
    ⟨hVW ht.2,hD.disk_subset_omittedDomain t.2 ht.2 n ht.1⟩)

end NLS.ZakharovShabat
