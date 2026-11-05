import NLS.ZakharovShabat.SourceDiagonalLaurentLocalChart
import NLS.ZakharovShabat.SourceHolomorphicRealCenteredBalls
import NLS.ComplexAnalysis.GlueHolomorphicCharts

/-! # Laurent actions on one neighborhood of the entire real diagonal

Fixed circles give the actual local contour functions. Their real gap
formula and the real-form identity theorem identify full complex overlaps.
The union is open before either the noncentral index or integer level is
chosen; in particular it is not an infinite intersection of neighborhoods.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourceDiagonalLaurentAtlas (hp : p ≠ ⊤) (hp1 : 1 < p) where
  localChart : (φ : realDiagonalSourceLocus p) → SourceDiagonalLaurentLocalChart hp hp1 φ

namespace SourceDiagonalLaurentAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} (A : SourceDiagonalLaurentAtlas hp hp1)

def sourceBall (φ : realDiagonalSourceLocus p) : Set (CoeffPair p) :=
  ball φ.val (A.localChart φ).radius

def domain : Set (CoeffPair p) := ⋃ φ, A.sourceBall φ

def action (n k : ℤ) : CoeffPair p → ℂ :=
  glueHolomorphicCharts A.sourceBall (fun φ => (A.localChart φ).action n k)

theorem isOpen_domain : IsOpen A.domain := isOpen_iUnion (fun _ => isOpen_ball)

theorem realDiagonal_subset_domain : realDiagonalSourceLocus p ⊆ A.domain := by
  intro φ hφ
  exact mem_iUnion.mpr ⟨⟨φ,hφ⟩,mem_ball_self (A.localChart ⟨φ,hφ⟩).radius_pos⟩

theorem localAction_eqOn (B : SourceDiagonalLaurentAtlas hp hp1)
    (φ θ : realDiagonalSourceLocus p) (n k : ℤ) (hn : n ≠ 0) :
    EqOn ((A.localChart φ).action n k) ((B.localChart θ).action n k)
      (A.sourceBall φ ∩ B.sourceBall θ) := by
  apply eqOn_sourceRealCenteredBalls_of_real_agreement hp ⟨φ.val,φ.property.1⟩ ⟨θ.val,θ.property.1⟩
    _ _ _ _ ((A.localChart φ).analytic_action n k hn).differentiableOn
    ((B.localChart θ).analytic_action n k hn).differentiableOn
  intro χ hχ
  exact ((A.localChart φ).action_eq_real ⟨χ.val,χ.property⟩ hχ.1 n k hn).trans
    ((B.localChart θ).action_eq_real ⟨χ.val,χ.property⟩ hχ.2 n k hn).symm

theorem action_eq_local (n k : ℤ) (hn : n ≠ 0) (φ : realDiagonalSourceLocus p) :
    EqOn (A.action n k) ((A.localChart φ).action n k) (A.sourceBall φ) :=
  glueHolomorphicCharts_eq_on A.sourceBall _ (fun χ θ => A.localAction_eqOn A χ θ n k hn) φ

theorem analytic_action (n k : ℤ) (hn : n ≠ 0) : AnalyticOnNhd ℂ (A.action n k) A.domain := by
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  have he := glueHolomorphicCharts_eventuallyEq A.sourceBall
    (fun χ => (A.localChart χ).action n k) (fun _ => isOpen_ball)
    (fun χ θ => A.localAction_eqOn A χ θ n k hn) φ ψ hφ
  exact ((A.localChart φ).analytic_action n k hn ψ hφ).congr he.symm

/-- Real agreement is valid also at real nondiagonal sources lying in
the complex neighborhood, which fixes every complex overlap uniquely. -/
theorem action_eq_real (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ A.domain)
    (n k : ℤ) (hn : n ≠ 0) : A.action n k φ.val = sourceRealLaurentAction hp hp1 φ n k := by
  obtain ⟨θ,hθ⟩ := mem_iUnion.mp hφ
  exact (A.action_eq_local n k hn θ hθ).trans ((A.localChart θ).action_eq_real φ hθ n k hn)

theorem action_eqOn (B : SourceDiagonalLaurentAtlas hp hp1) (n k : ℤ) (hn : n ≠ 0) :
    EqOn (A.action n k) (B.action n k) (A.domain ∩ B.domain) := by
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ.1
  obtain ⟨θ,hθ⟩ := mem_iUnion.mp hψ.2
  rw [A.action_eq_local n k hn φ hφ,B.action_eq_local n k hn θ hθ]
  exact A.localAction_eqOn B φ θ n k hn ⟨hφ,hθ⟩

/-- All noncentral integer levels are represented by one family of
actual zero-excluding isolating circles at every point of the domain. -/
theorem circle_representation (ψ : CoeffPair p) (hψ : ψ ∈ A.domain) :
    ∃ W : Set (CoeffPair p), ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ,
      ∀ n : ℤ, n ≠ 0 → 0 < R n ∧ (0 : ℂ) ∉ closedBall (c n) (R n) ∧
        sphere (c n) (R n) ⊆ sourceCanonicalRootDomain hp hp1 ψ ∧
        sourcePeriodicSegment hp hp1 ψ n ⊆ ball (c n) (R n) ∧
        closedBall (c n) (R n) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n ∧
        ∀ k : ℤ, A.action n k ψ = sourceLaurentPrimitiveCircle hp hp1 W n k ψ (c n) (R n) := by
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  let C := A.localChart φ
  have hψC := C.source_subset hφ
  refine ⟨C.ambient,C.cauchy.discs.center,C.contourRadius,?_⟩
  intro n hn
  refine ⟨C.contourRadius_pos n,C.zero_not_mem_contour_disc n hn,
    C.cauchy.intermediate_circle_root n ψ hψC _
      (C.contourRadius_bounds n).1 (C.contourRadius_bounds n).2,
    (C.cauchy.discs.segment_subset ψ hψC n).trans (ball_subset_ball (C.contourRadius_bounds n).1),
    (closedBall_subset_closedBall (C.contourRadius_bounds n).2.le).trans (C.cauchy.discs.avoids_other ψ hψC n),?_⟩
  intro k
  exact A.action_eq_local n k hn φ hφ

end SourceDiagonalLaurentAtlas

theorem exists_sourceDiagonalLaurentAtlas (hp : p ≠ ⊤) (hp1 : 1 < p) :
    Nonempty (SourceDiagonalLaurentAtlas hp hp1) :=
  ⟨⟨fun φ => Classical.choice (exists_sourceDiagonalLaurentLocalChart hp hp1 φ)⟩⟩

def sourceDiagonalLaurentAtlas (hp : p ≠ ⊤) (hp1 : 1 < p) : SourceDiagonalLaurentAtlas hp hp1 :=
  Classical.choice (exists_sourceDiagonalLaurentAtlas hp hp1)

def sourceDiagonalLaurentDomain (hp : p ≠ ⊤) (hp1 : 1 < p) : Set (CoeffPair p) :=
  (sourceDiagonalLaurentAtlas hp hp1).domain

def sourceDiagonalLaurentAction (hp : p ≠ ⊤) (hp1 : 1 < p) (n k : ℤ) : CoeffPair p → ℂ :=
  (sourceDiagonalLaurentAtlas hp hp1).action n k

theorem isOpen_sourceDiagonalLaurentDomain (hp : p ≠ ⊤) (hp1 : 1 < p) :
    IsOpen (sourceDiagonalLaurentDomain hp hp1) := (sourceDiagonalLaurentAtlas hp hp1).isOpen_domain

theorem realDiagonal_subset_sourceDiagonalLaurentDomain (hp : p ≠ ⊤) (hp1 : 1 < p) :
    realDiagonalSourceLocus p ⊆ sourceDiagonalLaurentDomain hp hp1 :=
  (sourceDiagonalLaurentAtlas hp hp1).realDiagonal_subset_domain

theorem analyticOnNhd_sourceDiagonalLaurentAction (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n k : ℤ) (hn : n ≠ 0) :
    AnalyticOnNhd ℂ (sourceDiagonalLaurentAction hp hp1 n k) (sourceDiagonalLaurentDomain hp hp1) :=
  (sourceDiagonalLaurentAtlas hp hp1).analytic_action n k hn

theorem sourceDiagonalLaurentAction_eq_real (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ sourceDiagonalLaurentDomain hp hp1)
    (n k : ℤ) (hn : n ≠ 0) :
    sourceDiagonalLaurentAction hp hp1 n k φ.val = sourceRealLaurentAction hp hp1 φ n k :=
  (sourceDiagonalLaurentAtlas hp hp1).action_eq_real φ hφ n k hn

end NLS.ZakharovShabat
