import NLS.ZakharovShabat.SourceRealActionLocalHolomorphic

/-!
# Local stability of the midpoint circle defining a real action

The filled midpoint disc at a real-type source avoids every other
periodic gap. Openness of the joint omitted-root domain and compactness
of that disc preserve this avoidance for nearby complex sources.
Continuity of the selected periodic endpoints keeps their segment
inside the same circle.
-/

noncomputable section
open Set Metric Filter Topology Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A midpoint circle representing the indexed real action remains an
isolating enclosing circle on a complex source neighborhood. -/
theorem exists_local_stable_midpointCircle_through_sourceRealAction
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (n : ℤ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential φ)
      (periodOnePotential_mem φ) n
    let d : ℝ := (r.re-l.re)/2
    ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      c = (((l.re+r.re)/2:ℝ):ℂ) ∧ d < R ∧
      ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
        sourceRealAction hp hp1 φ hreal n =
          sourceActionCircle hp hp1 φ c R ∧
        ∀ ψ ∈ V,
          sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R ∧
          closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) n
  let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
  let d : ℝ := (r.re-l.re)/2
  obtain ⟨ε,hε,hdisc⟩ :=
    exists_source_midpoint_closedBall_subset_omittedDomain
      hp hp1 φ hreal n
  let η : ℝ := ε/2
  have hη : η ∈ Ioc 0 ε := by
    dsimp [η]
    constructor <;> linarith
  let R : ℝ := d+η
  have hd : 0 ≤ d := by
    have hle := re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ)
        (periodOnePotential_mem φ)).2.1 n)
    dsimp [d]
    linarith
  have hR : 0 < R := by dsimp [R]; linarith [hη.1]
  have hother : closedBall c R ⊆
      sourceStandardRootOmittedDomain hp hp1 φ n := hdisc η hη
  have hseg : sourcePeriodicSegment hp hp1 φ n ⊆ ball c R :=
    sourcePeriodicSegment_subset_midpoint_ball
      hp hp1 φ hreal n η hη.1
  have hvalue : sourceRealAction hp hp1 φ hreal n =
      sourceActionCircle hp hp1 φ c R :=
    sourceRealAction_eq_enclosing_midpointCircle
      hp hp1 φ hreal n R (by change d < R; dsimp [R]; linarith [hη.1]) hother
  obtain ⟨W,_,_,hWreal,hdata⟩ :=
    exists_global_source_analytic_omittedJointProduct hp hp1
  let D := sourceStandardRootOmittedJointDomain hp hp1 W n
  have hDopen : IsOpen D := (hdata n).1
  have hprod : (closedBall c R) ×ˢ ({φ} : Set (CoeffPair p)) ⊆ D := by
    rintro ⟨z,ψ⟩ ⟨hz,hψ⟩
    have hψeq : ψ = φ := by simpa using hψ
    subst ψ
    exact ⟨hWreal hreal, hother hz⟩
  obtain ⟨U,Vfill,_,hVfillOpen,hKU,hφVfill,hUV⟩ :=
    generalized_tube_lemma (isCompact_closedBall c R)
      (isCompact_singleton : IsCompact ({φ} : Set (CoeffPair p)))
      hDopen hprod
  have hφVfill' : φ ∈ Vfill := hφVfill (by simp)
  have hfill (ψ : CoeffPair p) (hψ : ψ ∈ Vfill) :
      closedBall c R ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n := by
    intro z hz
    have hzD : (z,ψ) ∈ D := hUV ⟨hKU hz,hψ⟩
    exact hzD.2
  have hLbase : l ∈ ball c R := hseg (left_mem_segment ℝ l r)
  have hRbase : r ∈ ball c R := hseg (right_mem_segment ℝ l r)
  have hLnear : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n ∈ ball c R :=
    (continuousAt_canonicalPeriodicLeft_periodOne_of_realType
      hp hp1 φ hreal n).eventually (isOpen_ball.mem_nhds hLbase)
  have hRnear : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n ∈ ball c R :=
    (continuousAt_canonicalPeriodicRight_periodOne_of_realType
      hp hp1 φ hreal n).eventually (isOpen_ball.mem_nhds hRbase)
  have hnear : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n ∈ ball c R ∧
      canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n ∈ ball c R := by
    filter_upwards [hLnear,hRnear] with ψ hL hRt
    exact ⟨hL,hRt⟩
  obtain ⟨Vseg,hVsegSub,hVsegOpen,hφVseg⟩ := _root_.mem_nhds_iff.mp hnear
  let V := Vfill ∩ Vseg
  refine ⟨c,R,hR,rfl,?_,V,hVfillOpen.inter hVsegOpen,
    ⟨hφVfill',hφVseg⟩,hvalue,?_⟩
  · change d < R
    dsimp [R]
    linarith [hη.1]
  intro ψ hψ
  obtain ⟨hL,hRt⟩ := hVsegSub hψ.2
  have hsegment : sourcePeriodicSegment hp hp1 ψ n ⊆ ball c R := by
    change segment ℝ
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n)
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n) ⊆ ball c R
    exact (convex_ball c R).segment_subset hL hRt
  exact ⟨hsegment,hfill ψ hψ.1⟩

end NLS.ZakharovShabat
