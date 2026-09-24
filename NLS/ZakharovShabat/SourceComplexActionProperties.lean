import NLS.ZakharovShabat.SourceComplexAction

/-!
# Geometry and real restriction of the glued complex action

The union of real-centered action balls is connected because each
ball meets the connected real-type source locus. Complex
differentiability makes the glued action analytic along every complex
affine source line. On the real-type locus it retains the indexed
action's nonnegative sign and collapsed-gap zero criterion.
-/

noncomputable section
open Set Metric Filter Complex
open scoped ENNReal Topology
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The open domain of the glued complex action is connected. -/
theorem isConnected_sourceComplexActionDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    IsConnected (sourceComplexActionDomain hp hp1 n) := by
  let S := realTypeSourceLocus p
  let D := sourceComplexActionDomain hp hp1 n
  have hS : IsConnected S := isConnected_realTypeSourceLocus
  have hSD : S ⊆ D :=
    realTypeSourceLocus_subset_sourceComplexActionDomain hp hp1 n
  have h0S : (0 : CoeffPair p) ∈ S := by
    simp [S,realTypeSourceLocus]
  refine ⟨⟨0,hSD h0S⟩,isPreconnected_of_forall_pair ?_⟩
  intro x hx y hy
  obtain ⟨ch₀,hx₀⟩ := hx
  obtain ⟨ch₁,hy₁⟩ := hy
  let B₀ := ball ch₀.center ch₀.radius
  let B₁ := ball ch₁.center ch₁.radius
  let T := (S ∪ B₀) ∪ B₁
  have hB₀ : IsConnected B₀ := isConnected_ball ch₀.radius_pos
  have hB₁ : IsConnected B₁ := isConnected_ball ch₁.radius_pos
  have hSB₀ : (S ∩ B₀).Nonempty :=
    ⟨ch₀.center,ch₀.center_real,mem_ball_self ch₀.radius_pos⟩
  have hSB₁ : ((S ∪ B₀) ∩ B₁).Nonempty :=
    ⟨ch₁.center,Or.inl ch₁.center_real,mem_ball_self ch₁.radius_pos⟩
  have hT : IsConnected T :=
    (IsConnected.union hSB₁
      (IsConnected.union hSB₀ hS hB₀) hB₁)
  have hTD : T ⊆ D := by
    intro z hz
    rcases hz with (hz | hz) | hz
    · exact hSD hz
    · exact ⟨ch₀,hz⟩
    · exact ⟨ch₁,hz⟩
  refine ⟨T,hTD,?_,?_,hT.isPreconnected⟩
  · exact Or.inl (Or.inr hx₀)
  · exact Or.inr hy₁

/-- Every complex source direction through a point of the action
domain gives an analytic one-variable restriction. -/
theorem sourceComplexAction_analyticAlongLine_at
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hφ : φ ∈ sourceComplexActionDomain hp hp1 n)
    (h : CoeffPair p) :
    AnalyticAt ℂ (fun t : ℂ =>
      sourceComplexAction hp hp1 n (φ+t•h)) 0 := by
  let a : ℂ → CoeffPair p := fun t => φ+t•h
  have ha : Differentiable ℂ a := by
    dsimp [a]
    fun_prop
  let U : Set ℂ := a ⁻¹' sourceComplexActionDomain hp hp1 n
  have hUopen : IsOpen U :=
    (isOpen_sourceComplexActionDomain hp hp1 n).preimage ha.continuous
  have h0 : (0:ℂ) ∈ U := by simpa [U,a] using hφ
  have hline : DifferentiableOn ℂ
      (fun t : ℂ => sourceComplexAction hp hp1 n (a t)) U := by
    intro t ht
    have hdiffAt :=
      (sourceComplexAction_differentiableOn hp hp1 n (a t) ht).differentiableAt
        ((isOpen_sourceComplexActionDomain hp hp1 n).mem_nhds ht)
    exact (hdiffAt.comp t (ha t)).differentiableWithinAt
  exact hline.analyticAt (hUopen.mem_nhds h0)

/-- On real-type sources, the glued complex action is real and
nonnegative, and it vanishes exactly at a collapsed selected gap. -/
theorem sourceComplexAction_nonneg_and_eq_zero_iff_gap_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    0 ≤ (sourceComplexAction hp hp1 n φ).re ∧
    (sourceComplexAction hp hp1 n φ).im = 0 ∧
    (sourceComplexAction hp hp1 n φ = 0 ↔
      sourcePeriodicGapDisplacement hp hp1 φ n = 0) := by
  rw [sourceComplexAction_eq_sourceRealAction hp hp1 n φ hφ]
  exact sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 φ hφ n

end NLS.ZakharovShabat
