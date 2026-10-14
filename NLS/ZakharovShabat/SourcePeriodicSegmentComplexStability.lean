import NLS.ComplexAnalysis.ConnectedSetInBall
import NLS.ComplexAnalysis.SegmentIsolatingCircles
import NLS.ZakharovShabat.SourceEquation2_15

/-!
# Stability of an enclosed gap at complex sources

The ordered endpoints need not be continuous. Instead, openness of the
joint gap complement keeps a compact sphere disjoint from every gap.
Continuity of the midpoint then keeps the entire connected gap inside.
-/

noncomputable section
open Set Metric Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Any fixed enclosing circle in the joint root domain continues to
 enclose the selected gap near an arbitrary complex source in W. -/
theorem SourceEquation2_15Data.eventually_gap_subset_ball
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceEquation2_15Data hp hp1 W) (φ : CoeffPair p) (hφ : φ ∈ W)
    (n : ℤ) (a : ℂ) (r : ℝ)
    (hseg : sourcePeriodicSegment hp hp1 φ n ⊆ ball a r)
    (hsphere : sphere a r ⊆ sourceCanonicalRootDomain hp hp1 φ) :
    ∀ᶠ ψ in 𝓝 φ, sourcePeriodicSegment hp hp1 ψ n ⊆ ball a r := by
  have hslice : sphere a r ×ˢ ({φ} : Set (CoeffPair p)) ⊆
      sourceCanonicalRootJointDomain hp hp1 W := by
    rintro ⟨z,ψ⟩ ⟨hz,hψ⟩
    have he : ψ = φ := hψ
    subst ψ
    exact ⟨hφ,hsphere hz⟩
  obtain ⟨A,U,_,hU,hA,hφU,hAU⟩ :=
    generalized_tube_lemma (isCompact_sphere a r) isCompact_singleton h.joint.1 hslice
  have hm := (h.previous.previous.previous.previous.roots.roots.symmetric.midpoint n φ hφ).continuousAt
  have hevent : ∀ᶠ ψ in 𝓝 φ,
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ∈
        ball a r := hm (isOpen_ball.mem_nhds (hseg (sourcePeriodicMidpoint_mem_segment hp hp1 φ n)))
  filter_upwards [hU.mem_nhds (hφU (mem_singleton φ)),hevent] with ψ hψ hmid
  have hconn : IsPreconnected (sourcePeriodicSegment hp hp1 ψ n) :=
    (convex_segment _ _).isPreconnected
  apply subset_ball_of_isPreconnected_of_disjoint_sphere hconn a r
  · apply Set.disjoint_left.mpr
    intro z hz hzS
    have hzdom : (z,ψ) ∈ sourceCanonicalRootJointDomain hp hp1 W := hAU ⟨hA hzS,hψ⟩
    exact hzdom.2 n hz
  · exact ⟨_,sourcePeriodicMidpoint_mem_segment hp hp1 ψ n,hmid⟩

/-- A smaller enclosing radius persists locally inside any original disk.
The original source neighborhood and disk family are retained. -/
theorem SourceEquation2_15Data.local_originalDisk_gap_radius
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceEquation2_15Data hp hp1 W) (hV : IsOpen V) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφ : φ ∈ V) (n : ℤ) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧ U ⊆ V ∧
      ∃ a r R T : ℝ, 0 < r ∧ r < R ∧ R < T ∧ D n = ball (a : ℂ) T ∧
        ∀ ψ ∈ U, sourcePeriodicSegment hp hp1 ψ n ⊆ ball (a : ℂ) r := by
  obtain ⟨a,T,hT,he⟩ := hD.discs n
  have hseg : sourcePeriodicSegment hp hp1 φ n ⊆ ball (a : ℂ) T := by
    rw [← he]; exact hD.gap φ hφ n
  obtain ⟨r,R,hr,hrR,hRT,hsegr⟩ :=
    exists_nested_radii_of_segment_subset_ball _ _ (a : ℂ) T hseg
  have hother : closedBall (a : ℂ) r ⊆ sourceStandardRootOmittedDomain hp hp1 φ n := by
    apply Subset.trans (closedBall_subset_ball (hrR.trans hRT))
    rw [← he]
    exact hD.disk_subset_omittedDomain φ hφ n
  have hsphere := sourceCanonicalRootDomain_of_enclosingCircle hp hp1 φ n (a : ℂ) r hsegr hother
  have hev := h.eventually_gap_subset_ball φ (hVW hφ) n (a : ℂ) r hsegr hsphere
  obtain ⟨U,hUsub,hUopen,hφU⟩ := _root_.mem_nhds_iff.mp (hev.and (hV.mem_nhds hφ))
  exact ⟨U,hUopen,hφU,(fun ψ hψ => (hUsub hψ).2),a,r,R,T,hr,hrR,hRT,he,
    fun ψ hψ => (hUsub hψ).1⟩

end NLS.ZakharovShabat
