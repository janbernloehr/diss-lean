import NLS.ZakharovShabat.SourceCriticalRootPeriodCircle
import NLS.ZakharovShabat.SourceActionContourHomotopy
import NLS.ZakharovShabat.SourceActionContourFamily

/-!
# A circle-independent indexed action

The real centers and separation of the original disk families give a
cut-avoiding homotopy between their selected circles. Thus choosing any
such circle defines one indexed action. The simultaneous inner circles
from Section 11 compute the same function.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal unitInterval
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The weighted action is independent of the original circle family,
even when neither selected disk contains the other. -/
theorem SourceCriticalRootPeriodCircle.action_eq
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {n : ℤ}
    (D E : SourceCriticalRootPeriodCircle hp hp1 ψ n) :
    sourceActionCircle hp hp1 ψ (D.center : ℂ) D.radius =
      sourceActionCircle hp hp1 ψ (E.center : ℂ) E.radius :=
  sourceActionCircle_eq_of_homotopy_range hp hp1 ψ _ _ _ _
    (ContinuousMap.Homotopy.affine
      (circlePath (D.center : ℂ) D.radius : C(I,ℂ)) (circlePath (E.center : ℂ) E.radius))
    (affineHomotopy_loop (γ₁ := circlePath (D.center : ℂ) D.radius)
      (γ₂ := circlePath (E.center : ℂ) E.radius))
    (D.homotopy_range E)
    (affineHomotopy_contDiffOn (circlePath_contDiffOn _ _) (circlePath_contDiffOn _ _))

/-- The actual normalized action integral on any original isolating
circle. The default outside sources admitting such circles is not used on W. -/
def sourceIndexedAction (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) : ℂ := by
  classical
  exact if h : Nonempty (SourceCriticalRootPeriodCircle hp hp1 ψ n) then
    let D := Classical.choice h
    sourceActionCircle hp hp1 ψ (D.center : ℂ) D.radius
  else 0

/-- Every original circle computes the same indexed action. -/
theorem sourceIndexedAction_eq_circle
    {hp : p ≠ ⊤} {hp1 : 1 < p} {ψ : CoeffPair p} {n : ℤ}
    (D : SourceCriticalRootPeriodCircle hp hp1 ψ n) :
    sourceIndexedAction hp hp1 n ψ = sourceActionCircle hp hp1 ψ (D.center : ℂ) D.radius := by
  classical
  rw [sourceIndexedAction,dif_pos (show Nonempty (SourceCriticalRootPeriodCircle hp hp1 ψ n) from ⟨D⟩)]
  exact SourceCriticalRootPeriodCircle.action_eq _ D

/-- A whole original source neighborhood shares one fixed-circle formula. -/
theorem SourceIsolatingNeighborhoods.action_eq_originalCircle
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (n : ℤ) (a r : ℝ) (hr : 0 < r) (he : D n = ball (a : ℂ) r)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) :
    sourceIndexedAction hp hp1 n ψ = sourceActionCircle hp hp1 ψ (a : ℂ) r :=
  sourceIndexedAction_eq_circle (hD.periodCircle ψ hψ n a r hr he)

/-- The smaller Section 11 circle retains the original projection separation. -/
def SourceActionContourFamily.periodCircle
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (C : SourceActionContourFamily hp hp1 V D)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) : SourceCriticalRootPeriodCircle hp hp1 ψ n where
  center := C.center n
  radius := C.radius n
  radius_pos := (C.inner_pos n).trans (C.inner_lt n)
  gap := (C.gap ψ hψ n).trans (ball_subset_ball (C.inner_lt n).le)
  other := by
    let houter := hD.periodCircle ψ hψ n (C.center n) (C.outer n)
      (((C.inner_pos n).trans (C.inner_lt n)).trans (C.radius_lt n)) (C.original n)
    intro m hm w hw
    rcases houter.other m hm w hw with hl | hr
    · left
      change w.re < C.center n-C.outer n at hl
      linarith [C.radius_lt n]
    · right
      change C.center n+C.outer n < w.re at hr
      linarith [C.radius_lt n]

/-- The simultaneous circles strictly inside the original disks compute
the indexed action throughout their common source neighborhood. -/
theorem SourceActionContourFamily.indexedAction_eq_circle
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {c : ℝ} (C : SourceActionContourFamily hp hp1 V D)
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
    sourceIndexedAction hp hp1 n ψ = sourceActionCircle hp hp1 ψ (C.center n : ℂ) (C.radius n) :=
  sourceIndexedAction_eq_circle (C.periodCircle hD ψ hψ n)

end NLS.ZakharovShabat
