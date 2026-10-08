import NLS.ZakharovShabat.SourceHigherActionLocalChart
import NLS.ZakharovShabat.SourcePrimitivePowerAtlas
import NLS.ZakharovShabat.SourceRealActionRealCenteredCircle

/-! # Higher actions on a common complex neighborhood

The real-form identity theorem glues the actual defining contours. All
indices and levels share one open domain containing the real source locus.
Different atlases agree on their overlap.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

structure SourceHigherActionAtlas (hp : p ≠ ⊤) (hp1 : 1 < p) where
  localChart : (φ : realTypeSourceLocus p) → SourceHigherActionLocalChart hp hp1 φ

namespace SourceHigherActionAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} (A : SourceHigherActionAtlas hp hp1)

def sourceBall (φ : realTypeSourceLocus p) : Set (CoeffPair p) :=
  ball φ.val (A.localChart φ).radius

def domain : Set (CoeffPair p) := ⋃ φ, A.sourceBall φ

def localAction (φ : realTypeSourceLocus p) (n : ℤ) (k : ℕ) (ψ : CoeffPair p) : ℂ :=
  sourceHigherActionCircle hp hp1 ψ ((A.localChart φ).center n) ((A.localChart φ).contourRadius n) k

/-- The level is `k+1`; the off-domain default is zero. -/
def action (n : ℤ) (k : ℕ) : CoeffPair p → ℂ :=
  NLS.ComplexAnalysis.glueHolomorphicCharts A.sourceBall (fun φ => A.localAction φ n k)

theorem isOpen_domain : IsOpen A.domain := isOpen_iUnion (fun _ => isOpen_ball)

theorem realType_subset_domain : realTypeSourceLocus p ⊆ A.domain := by
  intro φ hφ
  exact mem_iUnion.mpr ⟨⟨φ,hφ⟩,mem_ball_self (A.localChart ⟨φ,hφ⟩).radius_pos⟩

/-- Compatibility holds throughout the complex overlap of any two source balls. -/
theorem localAction_eqOn (B : SourceHigherActionAtlas hp hp1)
    (φ θ : realTypeSourceLocus p) (n : ℤ) (k : ℕ) :
    EqOn (A.localAction φ n k) (B.localAction θ n k) (A.sourceBall φ ∩ B.sourceBall θ) := by
  apply eqOn_sourceRealCenteredBalls_of_real_agreement hp φ θ _ _ _ _
    ((A.localChart φ).analytic n k).differentiableOn
    ((B.localChart θ).analytic n k).differentiableOn
  intro χ hχ
  exact ((A.localChart φ).agrees_real ⟨χ.val,χ.property⟩ hχ.1 n k).trans
    ((B.localChart θ).agrees_real ⟨χ.val,χ.property⟩ hχ.2 n k).symm

theorem action_eq_local (n : ℤ) (k : ℕ) (φ : realTypeSourceLocus p) :
    EqOn (A.action n k) (A.localAction φ n k) (A.sourceBall φ) :=
  NLS.ComplexAnalysis.glueHolomorphicCharts_eq_on A.sourceBall _
    (fun χ θ => A.localAction_eqOn A χ θ n k) φ

theorem analytic_action (n : ℤ) (k : ℕ) : AnalyticOnNhd ℂ (A.action n k) A.domain := by
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  have he := NLS.ComplexAnalysis.glueHolomorphicCharts_eventuallyEq A.sourceBall
    (fun χ => A.localAction χ n k) (fun _ => isOpen_ball)
    (fun χ θ => A.localAction_eqOn A χ θ n k) φ ψ hφ
  exact ((A.localChart φ).analytic n k ψ hφ).congr he.symm

theorem action_eq_real (φ : realTypeSourceSubmodule p) (n : ℤ) (k : ℕ) :
    A.action n k φ.val = (sourceRealHigherAction hp hp1 φ n k : ℂ) := by
  have hφ : φ.val ∈ A.sourceBall ⟨φ.val,φ.property⟩ :=
    mem_ball_self (A.localChart ⟨φ.val,φ.property⟩).radius_pos
  exact (A.action_eq_local n k ⟨φ.val,φ.property⟩ hφ).trans
    ((A.localChart ⟨φ.val,φ.property⟩).agrees_real φ hφ n k)

theorem circle_representation (ψ : CoeffPair p) (hψ : ψ ∈ A.domain) :
    ∃ c : ℤ → ℂ, ∃ R : ℤ → ℝ, sourcePsiRealCenteredContourFamily hp hp1 ψ c R ∧
      ∀ (n : ℤ) (k : ℕ), A.action n k ψ = sourceHigherActionCircle hp hp1 ψ (c n) (R n) k := by
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  exact ⟨(A.localChart φ).center,(A.localChart φ).contourRadius,
    (A.localChart φ).family ψ hφ,fun n k => A.action_eq_local n k φ hφ⟩

theorem action_of_collapsed (ψ : CoeffPair p) (hψ : ψ ∈ A.domain) (n : ℤ)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0) (k : ℕ) : A.action n k ψ = 0 := by
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ
  exact (A.action_eq_local n k φ hφ).trans ((A.localChart φ).collapsed ψ hφ n hgap k)

/-- The constructed higher actions do not depend on the chosen atlas. -/
theorem action_eqOn (B : SourceHigherActionAtlas hp hp1) (n : ℤ) (k : ℕ) :
    EqOn (A.action n k) (B.action n k) (A.domain ∩ B.domain) := by
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ.1
  obtain ⟨θ,hθ⟩ := mem_iUnion.mp hψ.2
  rw [A.action_eq_local n k φ hφ,B.action_eq_local n k θ hθ]
  exact A.localAction_eqOn B φ θ n k ⟨hφ,hθ⟩

/-- Level one agrees with the original complex action on their common domain. -/
theorem action_zero (n : ℤ) : EqOn (A.action n 0) (sourceComplexAction hp hp1 n)
    (A.domain ∩ sourceComplexActionDomain hp hp1 n) := by
  intro ψ hψ
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp hψ.1
  obtain ⟨ch,hch⟩ := hψ.2
  rw [A.action_eq_local n 0 φ hφ,sourceComplexAction_eq_chart hp hp1 n ch ψ hch]
  apply eqOn_sourceRealCenteredBalls_of_real_agreement hp φ ⟨ch.center,ch.center_real⟩
    (A.localChart φ).radius ch.radius (A.localAction φ n 0)
    (fun χ => sourceActionCircle hp hp1 χ ch.spectralCenter ch.spectralRadius)
    ((A.localChart φ).analytic n 0).differentiableOn ch.differentiable ?_ ⟨hφ,hch⟩
  intro χ hχ
  have hf := (A.localChart φ).family χ.val hχ.1
  change sourceHigherActionCircle hp hp1 χ.val _ _ 0 = _
  rw [sourceHigherActionCircle_zero,← ch.agrees_real χ.val hχ.2 χ.property]
  exact (sourceRealAction_eq_realCentered_enclosingCircle hp hp1 χ.val χ.property n _ _
    (hf.1 n) (hf.2 n).1 (hf.2 n).2.1 (hf.2 n).2.2.1).symm

end SourceHigherActionAtlas

/-- The atlas is constructed from the actual spectral data. -/
theorem exists_sourceHigherActionAtlas (hp : p ≠ ⊤) (hp1 : 1 < p) :
    Nonempty (SourceHigherActionAtlas hp hp1) :=
  ⟨⟨fun φ => Classical.choice (exists_sourceHigherActionLocalChart hp hp1 φ)⟩⟩

/-- A fixed atlas supplies canonical functions; overlap compatibility proves
that any other valid atlas computes the same values on its common domain. -/
def sourceHigherActionAtlas (hp : p ≠ ⊤) (hp1 : 1 < p) : SourceHigherActionAtlas hp hp1 :=
  Classical.choice (exists_sourceHigherActionAtlas hp hp1)

def sourceComplexHigherActionDomain (hp : p ≠ ⊤) (hp1 : 1 < p) : Set (CoeffPair p) :=
  (sourceHigherActionAtlas hp hp1).domain

def sourceComplexHigherAction (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (k : ℕ) : CoeffPair p → ℂ :=
  (sourceHigherActionAtlas hp hp1).action n k

theorem isOpen_sourceComplexHigherActionDomain (hp : p ≠ ⊤) (hp1 : 1 < p) :
    IsOpen (sourceComplexHigherActionDomain hp hp1) := (sourceHigherActionAtlas hp hp1).isOpen_domain

theorem realType_subset_sourceComplexHigherActionDomain (hp : p ≠ ⊤) (hp1 : 1 < p) :
    realTypeSourceLocus p ⊆ sourceComplexHigherActionDomain hp hp1 :=
  (sourceHigherActionAtlas hp hp1).realType_subset_domain

theorem analyticOnNhd_sourceComplexHigherAction (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (k : ℕ) :
    AnalyticOnNhd ℂ (sourceComplexHigherAction hp hp1 n k) (sourceComplexHigherActionDomain hp hp1) :=
  (sourceHigherActionAtlas hp hp1).analytic_action n k

theorem sourceComplexHigherAction_eq_real (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (k : ℕ) :
    sourceComplexHigherAction hp hp1 n k φ.val = (sourceRealHigherAction hp hp1 φ n k : ℂ) :=
  (sourceHigherActionAtlas hp hp1).action_eq_real φ n k

theorem sourceComplexHigherAction_zero (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    EqOn (sourceComplexHigherAction hp hp1 n 0) (sourceComplexAction hp hp1 n)
      (sourceComplexHigherActionDomain hp hp1 ∩ sourceComplexActionDomain hp hp1 n) :=
  (sourceHigherActionAtlas hp hp1).action_zero n

theorem sourceComplexHigherAction_of_collapsed (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hψ : ψ ∈ sourceComplexHigherActionDomain hp hp1) (n : ℤ)
    (hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0) (k : ℕ) :
    sourceComplexHigherAction hp hp1 n k ψ = 0 :=
  (sourceHigherActionAtlas hp hp1).action_of_collapsed ψ hψ n hgap k

end NLS.ZakharovShabat
