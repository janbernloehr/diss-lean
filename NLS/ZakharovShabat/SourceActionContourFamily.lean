import NLS.ZakharovShabat.SourcePeriodicSegmentComplexStability
import NLS.ZakharovShabat.SourceNormalizedActionUniformTailCircles
import NLS.ComplexAnalysis.PiecewiseC1Loop

/-!
# The simultaneous original-disk contours at the start of Section 11

All signed indices share one complex source neighborhood. The original
isolating disks are unchanged; each circle has a fixed open annular
neighborhood avoiding every moving gap. Only finitely many circles differ
from the free-centered circles of radius 3π/16.
-/

noncomputable section
open Set Metric Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Three radii give a uniform gap enclosure, an integration circle and
its original isolating disk, simultaneously for all indices and sources. -/
structure SourceActionContourFamily (hp : p ≠ ⊤) (hp1 : 1 < p)
    (V : Set (CoeffPair p)) (D : ℤ → Set ℂ) where
  center : ℤ → ℝ
  inner : ℤ → ℝ
  radius : ℤ → ℝ
  outer : ℤ → ℝ
  inner_pos : ∀ n, 0 < inner n
  inner_lt : ∀ n, inner n < radius n
  radius_lt : ∀ n, radius n < outer n
  original : ∀ n, D n = ball (center n : ℂ) (outer n)
  gap : ∀ ψ ∈ V, ∀ n, sourcePeriodicSegment hp hp1 ψ n ⊆ ball (center n : ℂ) (inner n)
  tail : ∃ K : ℕ, ∀ n : ℤ, K < n.natAbs →
    center n = Real.pi*n ∧ inner n = Real.pi/8 ∧
      radius n = 3*Real.pi/16 ∧ outer n = Real.pi/4

namespace SourceActionContourFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ}

/-- The fixed open annular neighborhood U'_n of the integration circle. -/
def collar (C : SourceActionContourFamily hp hp1 V D) (n : ℤ) : Set ℂ :=
  ball (C.center n : ℂ) (C.outer n) \ closedBall (C.center n : ℂ) (C.inner n)

theorem collar_open (C : SourceActionContourFamily hp hp1 V D) (n : ℤ) :
    IsOpen (C.collar n) := isOpen_ball.sdiff isClosed_closedBall

theorem sphere_subset_collar (C : SourceActionContourFamily hp hp1 V D) (n : ℤ) :
    sphere (C.center n : ℂ) (C.radius n) ⊆ C.collar n := by
  intro z hz
  have he := mem_sphere.mp hz
  exact ⟨mem_ball.mpr (he ▸ C.radius_lt n),
    fun hz => (C.inner_lt n).not_ge (he ▸ mem_closedBall.mp hz)⟩

theorem closedBall_subset_original (C : SourceActionContourFamily hp hp1 V D) (n : ℤ) :
    closedBall (C.center n : ℂ) (C.radius n) ⊆ D n := by
  rw [C.original n]
  exact closedBall_subset_ball (C.radius_lt n)

/-- The full fixed collar lies in the original disk minus its moving gap. -/
theorem collar_subset_cutDisk (C : SourceActionContourFamily hp hp1 V D)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
    C.collar n ⊆ D n \ sourcePeriodicSegment hp hp1 ψ n := by
  intro z hz
  refine ⟨?_,fun hgap => hz.2 (ball_subset_closedBall (C.gap ψ hψ n hgap))⟩
  rw [C.original n]
  exact hz.1

/-- Isolation excludes every other gap from the same collar. -/
theorem collar_subset_rootDomain (C : SourceActionContourFamily hp hp1 V D)
    {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
    C.collar n ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
  intro z hz m
  have hzD := C.collar_subset_cutDisk ψ hψ n hz
  by_cases hm : m = n
  · subst m; exact hzD.2
  · exact hD.disk_subset_omittedDomain ψ hψ n hzD.1 m hm

/-- The chosen orientation makes one positive turn around every point
of the selected gap, including a collapsed gap. -/
theorem windingIntegral_eq_one (C : SourceActionContourFamily hp hp1 V D)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) (z : ℂ)
    (hz : z ∈ sourcePeriodicSegment hp hp1 ψ n) :
    (PiecewiseC1Loop.circle (C.center n : ℂ) (C.radius n)).windingIntegral z = 1 :=
  PiecewiseC1Loop.windingIntegral_circle _ _ _
    (ball_subset_ball (C.inner_lt n).le (C.gap ψ hψ n hz))

end SourceActionContourFamily

/-- At every complex source in W, one connected source neighborhood
supports all contours and collars inside the given original disk family. -/
theorem SourceEquation2_15Data.original_contourFamily
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (h : SourceEquation2_15Data hp hp1 W) (hV : IsOpen V) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (φ : CoeffPair p) (hφ : φ ∈ V) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ φ ∈ U ∧ U ⊆ V ∧
      Nonempty (SourceActionContourFamily hp hp1 U D) := by
  classical
  obtain ⟨K₀,Vtail,hVtail,hφtail,htail⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circles hp hp1 φ
  obtain ⟨N,hN⟩ := hD.tail
  let K := max K₀ N
  have hlocal := fun n => h.local_originalDisk_gap_radius hV hVW hD φ hφ n
  choose Vhead hVo hφhead hVsub a r R T hr hrR hRT he hhead using hlocal
  let s : Finset ℤ := Finset.Icc (-(K : ℤ)) K
  let Vheads : Set (CoeffPair p) := ⋂ n ∈ s, Vhead n
  have hVheads : IsOpen Vheads := isOpen_biInter_finset (fun n _ => hVo n)
  have hφheads : φ ∈ Vheads := by
    simp only [Vheads,mem_iInter]
    exact fun n _ => hφhead n
  obtain ⟨ε,hε,hεsub⟩ := Metric.mem_nhds_iff.mp
    (((hVtail.inter hV).inter hVheads).mem_nhds ⟨⟨hφtail,hφ⟩,hφheads⟩)
  let U := ball φ ε
  have hUV : U ⊆ V := fun ψ hψ => (hεsub hψ).1.2
  let ac : ℤ → ℝ := fun n => if n ∈ s then a n else Real.pi*n
  let ri : ℤ → ℝ := fun n => if n ∈ s then r n else Real.pi/8
  let rc : ℤ → ℝ := fun n => if n ∈ s then R n else 3*Real.pi/16
  let ro : ℤ → ℝ := fun n => if n ∈ s then T n else Real.pi/4
  have hnot (n : ℤ) (hn : n ∉ s) : K < n.natAbs := by
    simp only [s,Finset.mem_Icc] at hn
    omega
  refine ⟨U,isOpen_ball,isConnected_ball hε,mem_ball_self hε,hUV,
    ⟨⟨ac,ri,rc,ro,?_,?_,?_,?_,?_,?_⟩⟩⟩
  · intro n
    dsimp [ri]
    split_ifs with hn
    · exact hr n
    · positivity
  · intro n
    dsimp [ri,rc]
    split_ifs with hn
    · exact hrR n
    · nlinarith [Real.pi_pos]
  · intro n
    dsimp [rc,ro]
    split_ifs with hn
    · exact hRT n
    · nlinarith [Real.pi_pos]
  · intro n
    by_cases hn : n ∈ s
    · simpa only [ac,ro,if_pos hn] using he n
    · have hnN : N < n.natAbs := lt_of_le_of_lt (le_max_right K₀ N) (hnot n hn)
      simpa only [ac,ro,if_neg hn,Complex.ofReal_mul,Complex.ofReal_intCast,
        refinedResonantDisk] using hN n hnN
  · intro ψ hψ n
    by_cases hn : n ∈ s
    · have hψhead : ψ ∈ Vhead n := mem_iInter₂.mp (hεsub hψ).2 n hn
      simpa only [ac,ri,if_pos hn] using hhead n ψ hψhead
    · have hnK₀ : K₀ ≤ n.natAbs := (le_max_left K₀ N).trans (hnot n hn).le
      simpa only [ac,ri,if_neg hn,Complex.ofReal_mul,Complex.ofReal_intCast] using
        (htail ψ (hεsub hψ).1.1 n hnK₀).1
  · refine ⟨K,fun n hn => ?_⟩
    have hns : n ∉ s := by simp only [s,Finset.mem_Icc]; omega
    simp only [ac,ri,rc,ro,if_neg hns,and_self]

end NLS.ZakharovShabat
