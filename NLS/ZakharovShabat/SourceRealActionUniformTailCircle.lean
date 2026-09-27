import NLS.ZakharovShabat.SourceNormalizedActionCircleHomotopy
import NLS.ZakharovShabat.SourceRealActionEnclosingCircle

/-!
# The real indexed action on common distant circles

A midpoint-centered sixteenth-π circle encloses each distant real
gap and fits inside the common free-centered eighth-π circle.
Nested contour invariance transfers the real-action formula.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Tiny midpoint and gap displacements identify the real indexed
action with the fixed free-centered eighth-π circle. -/
theorem sourceRealAction_eq_free_eighth_circle_of_tiny_midgap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hmid : ‖sourceStandardRootMidpoint hp hp1 ψ n - (Real.pi:ℂ)*n‖ ≤
      Real.pi/64)
    (hgap : ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ ≤ Real.pi/32)
    (hother : closedBall ((Real.pi:ℂ)*n) (Real.pi/8) ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sourceRealAction hp hp1 ψ hreal n =
      sourceActionCircle hp hp1 ψ ((Real.pi:ℂ)*n) (Real.pi/8) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let τ := sourceStandardRootMidpoint hp hp1 ψ n
  let c : ℂ := (Real.pi:ℂ)*n
  let m : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
  let d : ℝ := (r.re-l.re)/2
  have him := canonicalPeriodicEndpoints_im_eq_zero_of_realType
    hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ)
      (isRealType_periodOnePotential ψ hreal) n
  have himl : l.im = 0 := him.1
  have himr : r.im = 0 := him.2
  have hτeq : τ = (l+r)/2 := rfl
  have hmτ : m = τ := by
    rw [hτeq]
    apply Complex.ext
    · simp [m,Complex.add_re]
    · simp [m,Complex.add_im,himl,himr]
  have hgre : r.re-l.re ≤ ‖r-l‖ := by
    simpa only [Complex.sub_re] using Complex.re_le_norm (r-l)
  have hgnorm : ‖r-l‖ ≤ Real.pi/32 := by
    simpa only [r,l,sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap]
      using hgap
  have hd : d ≤ Real.pi/64 := by dsimp [d]; linarith
  have hρ : 0 < Real.pi/16-d := by
    dsimp [d] at hd ⊢
    nlinarith [Real.pi_pos]
  have hseginner : sourcePeriodicSegment hp hp1 ψ n ⊆
      ball τ (Real.pi/16) := by
    have h := sourcePeriodicSegment_subset_midpoint_ball
      hp hp1 ψ hreal n (Real.pi/16-d) hρ
    change sourcePeriodicSegment hp hp1 ψ n ⊆
      ball m (d+(Real.pi/16-d)) at h
    have hrad : d+(Real.pi/16-d)=Real.pi/16 := by ring
    rw [hrad] at h
    simpa only [hmτ] using h
  have hsegouter : sourcePeriodicSegment hp hp1 ψ n ⊆
      ball c (Real.pi/8) :=
    sourcePeriodicSegment_subset_free_eighth_ball hp hp1 ψ n hmid hgap
  have hnest : closedBall τ (Real.pi/16) ⊆ closedBall c (Real.pi/8) := by
    intro z hz
    have hzτ : dist z τ ≤ Real.pi/16 := mem_closedBall.mp hz
    have hτc : dist τ c ≤ Real.pi/64 := by
      simpa only [τ,c,dist_eq_norm] using hmid
    have htri := dist_triangle z τ c
    apply mem_closedBall.mpr
    nlinarith [Real.pi_pos]
  have hinnerother : closedBall τ (Real.pi/16) ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n := hnest.trans hother
  have hdlt : d < Real.pi/16 := by nlinarith [Real.pi_pos]
  have hotherMid : closedBall m (Real.pi/16) ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n := by
    rw [hmτ]
    exact hinnerother
  have hrealMid : sourceRealAction hp hp1 ψ hreal n =
      sourceActionCircle hp hp1 ψ τ (Real.pi/16) := by
    have h := sourceRealAction_eq_enclosing_midpointCircle
      hp hp1 ψ hreal n (Real.pi/16) hdlt hotherMid
    change sourceRealAction hp hp1 ψ hreal n =
      sourceActionCircle hp hp1 ψ m (Real.pi/16) at h
    simpa only [hmτ] using h
  calc
    sourceRealAction hp hp1 ψ hreal n =
        sourceActionCircle hp hp1 ψ τ (Real.pi/16) := hrealMid
    _ = sourceActionCircle hp hp1 ψ c (Real.pi/8) :=
      sourceActionCircle_eq_of_nested_enclosingCircles hp hp1 ψ n
        τ c (Real.pi/16) (Real.pi/8)
        (by positivity) (by positivity)
        hseginner hsegouter hnest hother

/-- One neighborhood and cutoff make the free-centered circles
compute every distant indexed real action at real-type sources. -/
theorem exists_local_sourceRealAction_eq_free_eighth_circle_tail
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ K : ℕ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ hψ : IsRealType (CoeffPair.toMax p ψ),
        ∀ n : ℤ, K ≤ n.natAbs →
          sourceRealAction hp hp1 ψ hψ n =
            sourceActionCircle hp hp1 ψ ((Real.pi:ℂ)*n) (Real.pi/8) := by
  obtain ⟨Kt,Vt,hVtopen,hφVt,htiny⟩ :=
    exists_local_sourcePeriodicMidpointGap_tiny_tail hp hp1 φ
  obtain ⟨Kc,Vc,hVcopen,hφVc,hcircle⟩ :=
    exists_local_sourceNormalizedAction_uniform_tail_circle_data hp hp1 φ hφ
  let K := max Kt Kc
  refine ⟨K,Vt ∩ Vc,hVtopen.inter hVcopen,⟨hφVt,hφVc⟩,?_⟩
  intro ψ hψ hreal n hn
  have hKt : Kt ≤ n.natAbs := le_trans (le_max_left _ _) hn
  have hKc : Kc ≤ n.natAbs := le_trans (le_max_right _ _) hn
  obtain ⟨hmid,hgap⟩ := htiny ψ hψ.1 n hKt
  have hother := (hcircle ψ hψ.2 n hKc).2.1
  exact sourceRealAction_eq_free_eighth_circle_of_tiny_midgap
    hp hp1 ψ hreal n hmid hgap hother

end NLS.ZakharovShabat
