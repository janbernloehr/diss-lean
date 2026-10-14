import NLS.ZakharovShabat.SourceLemma10_5
import NLS.ZakharovShabat.SourceCanonicalRootJointAnalytic
import Mathlib.Topology.MetricSpace.Algebra

/-!
# The canonical-root product on unchanged analytic domains

The literal symmetric cutoffs converge locally uniformly on the original
common domain. The fixed local family retains its source neighborhood,
isolating disks and distance constant, including for collapsed-gap extensions.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The same common domain supports the complete canonical product. -/
theorem SourceLemma10_5Data.canonicalJoint
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) :
    IsOpen (sourceCanonicalRootJointDomain hp hp1 W) ∧
    AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1)
      (sourceCanonicalRootJointDomain hp hp1 W) := by
  constructor
  · rw [sourceCanonicalRootJointDomain_eq_inter_omitted]
    exact (h.joint 0).1.inter (h.joint 1).1
  · intro q hq
    have hroot := h.roots.joint 0 q ⟨hq.1,hq.2 0⟩
    have hprod := (h.joint 0).2 q ⟨hq.1,fun m _ => hq.2 m⟩
    have he : sourceCanonicalRootJointProduct hp hp1 = fun t : ℂ × CoeffPair p =>
        2*Complex.I * sourceStandardRoot hp hp1 t.2 0 t.1 *
          sourceStandardRootOmittedJointProduct hp hp1 0 t := by
      funext t
      exact sourceCanonicalRoot_eq_omitted hp hp1 0 t.2 t.1
    rw [he]
    exact (analyticAt_const.mul hroot).mul hprod

/-- The literal closed-disk complement uses the original V,D,c. -/
theorem SourceLemma10_5Data.canonicalClosedFixed
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c) :
    AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1)
      ((⋃ m : ℤ, closure (D m))ᶜ ×ˢ V) := by
  apply h.canonicalJoint.2.mono
  intro q hq
  refine ⟨hVW hq.2,?_⟩
  intro m hm
  exact hq.1 (mem_iUnion.mpr ⟨m,subset_closure (hD.gap q.2 hq.2 m hm)⟩)

/-- The natural domain is exactly the printed complement of the gap union. -/
theorem sourceCanonicalRootDomain_eq_compl_iUnion (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) :
    sourceCanonicalRootDomain hp hp1 ψ = (⋃ m : ℤ, sourcePeriodicSegment hp hp1 ψ m)ᶜ := by
  ext z
  simp [sourceCanonicalRootDomain]

/-- The literal full cutoffs converge jointly locally uniformly on the unchanged moving-gap domain. -/
theorem SourceLemma10_5Data.canonicalLocallyUniform
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) :
    TendstoLocallyUniformlyOn (fun N (q : ℂ × CoeffPair p) =>
      sourceCanonicalRootPartialProduct hp hp1 N q.2 q.1)
      (sourceCanonicalRootJointProduct hp hp1) atTop
      (sourceCanonicalRootJointDomain hp hp1 W) := by
  let Q := sourceCanonicalRootJointDomain hp hp1 W
  let R : ℂ × CoeffPair p → ℂ := fun q => 2*Complex.I*sourceStandardRoot hp hp1 q.2 0 q.1
  have hsub : Q ⊆ sourceStandardRootOmittedJointDomain hp hp1 W 0 :=
    fun q hq => ⟨hq.1,fun m _ => hq.2 m⟩
  have hR : ContinuousOn R Q := by
    intro q hq
    exact (continuousAt_const.mul (h.roots.joint 0 q ⟨hq.1,hq.2 0⟩).continuousAt).continuousWithinAt
  have hRu : TendstoUniformlyOn (fun _ : ℕ => R) R atTop Q := by
    intro u hu
    exact Filter.Eventually.of_forall (fun _ q _ => refl_mem_uniformity hu)
  have hm := hRu.tendstoLocallyUniformlyOn.mul₀ ((h.locally_uniform 0).mono hsub)
    hR ((h.joint 0).2.continuousOn.mono hsub)
  have hf := hm.congr (fun N q _ =>
    (sourceCanonicalRootPartialProduct_eq_omitted hp hp1 0 N (by omega) q.2 q.1).symm)
  apply hf.congr_right
  intro q _
  exact (sourceCanonicalRoot_eq_omitted hp hp1 0 q.2 q.1).symm

/-- A collapsed gap gives an analytic continuation on the original selected disk. -/
theorem SourceLemma10_5Data.canonicalCollapsedDisk
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0) :
    AnalyticOnNhd ℂ (sourceCanonicalRoot hp hp1 ψ) (D n) :=
  (sourceCanonicalRoot_analyticOnNhd_of_zeroGap hp hp1 W n (h.joint n).2 ψ (hVW hψ) hg).mono
    (hD.disk_subset_omittedDomain ψ hψ n)

/-- The literal symmetric cutoffs converge uniformly on compact subsets of the full joint domain. -/
theorem SourceLemma10_5Data.canonicalCompact
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (K : Set (ℂ × CoeffPair p)) (hK : IsCompact K)
    (hsub : K ⊆ sourceCanonicalRootJointDomain hp hp1 W) :
    TendstoUniformlyOn (fun N (q : ℂ × CoeffPair p) => sourceCanonicalRootPartialProduct hp hp1 N q.2 q.1)
      (sourceCanonicalRootJointProduct hp hp1) atTop K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    (h.canonicalLocallyUniform.mono hsub)

/-- At a fixed source, convergence is uniform on every compact subset of the spectral gap complement. -/
theorem SourceLemma10_5Data.canonicalSpectralCompact
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceLemma10_5Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (K : Set ℂ) (hK : IsCompact K) (hsub : K ⊆ sourceCanonicalRootDomain hp hp1 ψ) :
    TendstoUniformlyOn (fun N => sourceCanonicalRootPartialProduct hp hp1 N ψ)
      (sourceCanonicalRoot hp hp1 ψ) atTop K := by
  have hi : IsCompact ((fun z : ℂ => (z,ψ)) '' K) := hK.image (continuous_id.prodMk continuous_const)
  have hc := h.canonicalCompact _ hi (by
    rintro q ⟨z,hz,rfl⟩
    exact ⟨hψ,hsub hz⟩)
  intro u hu
  filter_upwards [hc u hu] with N hN
  intro z hz
  exact hN (z,ψ) ⟨z,hz,rfl⟩

end NLS.ZakharovShabat
