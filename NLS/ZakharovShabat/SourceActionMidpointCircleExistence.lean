import NLS.ZakharovShabat.SourceActionMidpointCircleCharacterization
import NLS.ZakharovShabat.CanonicalPeriodicGapOrder

/-!
# Isolating midpoint circles at real-type sources

Strict separation from the neighboring real periodic gaps leaves a
positive radial margin around the selected midpoint circle. Every
filled disc within that margin avoids all other gap segments.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A real-type source has a positive margin of midpoint-centered
filled discs enclosing each selected gap and avoiding all other gaps. -/
theorem exists_source_midpoint_closedBall_subset_omittedDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∃ ε : ℝ, 0 < ε ∧ ∀ η ∈ Ioc 0 ε,
      closedBall c (d+η) ⊆ sourceStandardRootOmittedDomain hp hp1 ψ n := by
  let φ := periodOnePotential ψ
  let l := canonicalPeriodicLeft hp hp1 φ (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 φ (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
  let d : ℝ := (r.re-l.re)/2
  let u : ℝ := (canonicalPeriodicRight hp hp1 φ
    (periodOnePotential_mem ψ) (n-1)).re
  let v : ℝ := (canonicalPeriodicLeft hp hp1 φ
    (periodOnePotential_mem ψ) (n+1)).re
  have hu : u < l.re := by
    exact canonicalPeriodicRight_re_lt_left_of_lt
      hp hp1 φ (periodOnePotential_mem ψ)
      (isRealType_periodOnePotential ψ hreal) (by omega : n-1<n)
  have hv : r.re < v := by
    exact canonicalPeriodicRight_re_lt_left_of_lt
      hp hp1 φ (periodOnePotential_mem ψ)
      (isRealType_periodOnePotential ψ hreal) (by omega : n<n+1)
  let ε : ℝ := min (l.re-u) (v-r.re)/2
  have hε : 0 < ε := by
    dsimp [ε]
    exact div_pos (lt_min (sub_pos.mpr hu) (sub_pos.mpr hv)) (by norm_num)
  have hεu : ε < l.re-u := by
    dsimp [ε]
    have h := min_le_left (l.re-u) (v-r.re)
    linarith
  have hεv : ε < v-r.re := by
    dsimp [ε]
    have h := min_le_right (l.re-u) (v-r.re)
    linarith
  refine ⟨ε,hε,?_⟩
  intro η hη z hz m hmn hmem
  have hηu : η < l.re-u := lt_of_le_of_lt hη.2 hεu
  have hηv : η < v-r.re := lt_of_le_of_lt hη.2 hεv
  have hyim : z.im = 0 :=
    sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 ψ hreal m z hmem
  have hcim : c.im = 0 := by simp [c]
  have hproj : |z.re-c.re| ≤ d+η := by
    rw [← sourceRealPoints_dist_eq_abs_re_sub z c hyim hcim]
    exact mem_closedBall.mp hz
  have hbounds : l.re-η ≤ z.re ∧ z.re ≤ r.re+η := by
    have h := abs_le.mp hproj
    dsimp [c,d] at h
    constructor <;> linarith [h.1,h.2]
  have hI := sourcePeriodicSegment_re_mem_Icc hp hp1 ψ m z hmem
  rcases lt_or_gt_of_ne hmn with hm | hm
  · have hzu : z.re ≤ u := by
      by_cases he : m = n-1
      · subst m
        exact hI.2
      · have hmn' : m < n-1 := by omega
        have hord := canonicalPeriodicRight_re_lt_left_of_lt
          hp hp1 φ (periodOnePotential_mem ψ)
          (isRealType_periodOnePotential ψ hreal) hmn'
        have hwithin := re_le_of_complexLexLE
          ((canonicalPeriodicEndpoints_spec hp hp1 φ
            (periodOnePotential_mem ψ)).2.1 (n-1))
        exact hI.2.trans (hord.le.trans hwithin)
    linarith
  · have hvz : v ≤ z.re := by
      by_cases he : m = n+1
      · subst m
        exact hI.1
      · have hnm' : n+1 < m := by omega
        have hord := canonicalPeriodicRight_re_lt_left_of_lt
          hp hp1 φ (periodOnePotential_mem ψ)
          (isRealType_periodOnePotential ψ hreal) hnm'
        have hwithin := re_le_of_complexLexLE
          ((canonicalPeriodicEndpoints_spec hp hp1 φ
            (periodOnePotential_mem ψ)).2.1 (n+1))
        exact (hwithin.trans hord.le).trans hI.1
    linarith

/-- Every real-type source admits a whole interval of midpoint circles
on which the action is real, nonnegative, and zero precisely for a
collapsed selected gap. -/
theorem exists_sourceActionCircle_nonneg_and_zero_iff_gap_zero_midpoint
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∃ ε : ℝ, 0 < ε ∧ ∀ η ∈ Ioc 0 ε,
      0 ≤ (sourceActionCircle hp hp1 ψ c (d+η)).re ∧
        (sourceActionCircle hp hp1 ψ c (d+η)).im = 0 ∧
        (sourceActionCircle hp hp1 ψ c (d+η) = 0 ↔
          sourcePeriodicGapDisplacement hp hp1 ψ n = 0) := by
  let d : ℝ :=
    ((canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re -
     (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re)/2
  obtain ⟨ε,hε,hdisc⟩ :=
    exists_source_midpoint_closedBall_subset_omittedDomain
      hp hp1 ψ hreal n
  refine ⟨ε,hε,?_⟩
  intro η hη
  exact sourceActionCircle_nonneg_and_eq_zero_iff_gap_zero_on_midpointCircle
    hp hp1 ψ hreal n (d+η) (by change d < d+η; linarith [hη.1])
      (hdisc η hη)

end NLS.ZakharovShabat
