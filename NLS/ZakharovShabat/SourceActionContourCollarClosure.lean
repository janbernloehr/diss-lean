import NLS.ZakharovShabat.SourceSection11Contours

/-!
# Contour collars with their closures inside the original cut disks

The overline in the opening of Section 11 requires the closure of the
fixed open collar to avoid the moving gap. Two intermediate radii keep
that closure inside the existing collar, without changing the circles,
original isolating disks or common source neighborhood.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace SourceActionContourFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)} {D : ℤ → Set ℂ}

/-- A smaller fixed open collar, with a margin on both sides of its circle. -/
def compactCollar (C : SourceActionContourFamily hp hp1 V D) (n : ℤ) : Set ℂ :=
  ball (C.center n : ℂ) ((C.radius n+C.outer n)/2) \
    closedBall (C.center n : ℂ) ((C.inner n+C.radius n)/2)

theorem compactCollar_open (C : SourceActionContourFamily hp hp1 V D) (n : ℤ) :
    IsOpen (C.compactCollar n) := isOpen_ball.sdiff isClosed_closedBall

theorem sphere_subset_compactCollar (C : SourceActionContourFamily hp hp1 V D) (n : ℤ) :
    sphere (C.center n : ℂ) (C.radius n) ⊆ C.compactCollar n := by
  intro z hz
  have he := mem_sphere.mp hz
  refine ⟨mem_ball.mpr ?_, fun h => ?_⟩
  · rw [he]
    linarith [C.radius_lt n]
  · have hle := mem_closedBall.mp h
    rw [he] at hle
    linarith [C.inner_lt n]

/-- The entire closure stays in the original open collar. -/
theorem closure_compactCollar_subset_collar
    (C : SourceActionContourFamily hp hp1 V D) (n : ℤ) :
    closure (C.compactCollar n) ⊆ C.collar n := by
  have hs : C.compactCollar n ⊆
      closedBall (C.center n : ℂ) ((C.radius n+C.outer n)/2) \
        ball (C.center n : ℂ) ((C.inner n+C.radius n)/2) :=
    fun z hz => ⟨ball_subset_closedBall hz.1, fun hb => hz.2 (ball_subset_closedBall hb)⟩
  have hcl := closure_minimal hs (isClosed_closedBall.sdiff isOpen_ball)
  intro z hz
  obtain ⟨houter,hinner⟩ := hcl hz
  refine ⟨mem_ball.mpr ?_, fun h => ?_⟩
  · have ho := mem_closedBall.mp houter
    linarith [C.radius_lt n]
  · have hi := mem_closedBall.mp h
    apply hinner
    apply mem_ball.mpr
    linarith [C.inner_lt n]

/-- The printed closed-collar containment holds for every nearby source. -/
theorem closure_compactCollar_subset_cutDisk
    (C : SourceActionContourFamily hp hp1 V D)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
    closure (C.compactCollar n) ⊆ D n \ sourcePeriodicSegment hp hp1 ψ n :=
  (C.closure_compactCollar_subset_collar n).trans (C.collar_subset_cutDisk ψ hψ n)

/-- Isolation also excludes all other gaps from the same closed collar. -/
theorem closure_compactCollar_subset_rootDomain
    (C : SourceActionContourFamily hp hp1 V D)
    {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
    closure (C.compactCollar n) ⊆ sourceCanonicalRootDomain hp hp1 ψ :=
  (C.closure_compactCollar_subset_collar n).trans (C.collar_subset_rootDomain hD ψ hψ n)

/-- Joint analyticity holds in a neighborhood of every point of the closed collar. -/
theorem analytic_integrand_on_compactCollar_closure
    {W : Set (CoeffPair p)} (h : SourceEquation2_15Data hp hp1 W) (hVW : V ⊆ W)
    {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (C : SourceActionContourFamily hp hp1 V D) (n : ℤ) :
    AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p =>
      t.1 * deriv (canonicalDiscriminant hp (periodOnePotential t.2)) t.1 /
        sourceCanonicalRoot hp hp1 t.2 t.1) (closure (C.compactCollar n) ×ˢ V) :=
  (C.analytic_integrand_on_collar h hVW hD n).mono
    (fun _ ht => ⟨C.closure_compactCollar_subset_collar n ht.1,ht.2⟩)

end SourceActionContourFamily

/-- One source neighborhood supports every circle and every closed collar,
retaining the original disks and the preceding Section 11 data. -/
theorem SourceSection11ContourData.neighborhoods_with_collar_closures
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceSection11ContourData hp hp1 W) (φ : CoeffPair p) (hφ : φ ∈ W) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ IsConnected U ∧ φ ∈ U ∧ U ⊆ W ∧
      ∃ D c, SourceIsolatingNeighborhoods hp hp1 U D c ∧
        ∃ C : SourceActionContourFamily hp hp1 U D, ∀ n : ℤ,
          IsOpen (C.compactCollar n) ∧
          sphere (C.center n : ℂ) (C.radius n) ⊆ C.compactCollar n ∧
          (∀ ψ ∈ U, closure (C.compactCollar n) ⊆ D n \ sourcePeriodicSegment hp hp1 ψ n) ∧
          AnalyticOnNhd ℂ (fun t : ℂ × CoeffPair p =>
            t.1 * deriv (canonicalDiscriminant hp (periodOnePotential t.2)) t.1 /
              sourceCanonicalRoot hp hp1 t.2 t.1) (closure (C.compactCollar n) ×ˢ U) ∧
          AnalyticOnNhd ℂ (fun ψ => sourceActionCircle hp hp1 ψ (C.center n : ℂ) (C.radius n)) U := by
  obtain ⟨U,hU,hUc,hφU,hUW,D,c,hD,C,ha⟩ := H.neighborhoods φ hφ
  refine ⟨U,hU,hUc,hφU,hUW,D,c,hD,C,fun n => ?_⟩
  exact ⟨C.compactCollar_open n,C.sphere_subset_compactCollar n,
    fun ψ hψ => C.closure_compactCollar_subset_cutDisk ψ hψ n,
    C.analytic_integrand_on_compactCollar_closure H.previous.previous.previous.previous hUW hD n,
    (ha n).2⟩

end NLS.ZakharovShabat
