import NLS.ZakharovShabat.SourceCriticalRootRatioEndpointCircleBound
import NLS.ComplexAnalysis.StadiumCircleCorners
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# Outer endpoint semicircles avoid the periodic cuts

The left and right outward half-circles stay off the selected real gap.
A uniform thickening of that gap avoids every other periodic cut. Thus
both arcs lie in the full canonical-root domain for a common small radius.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Real coordinates of a point on a real periodic gap lie between its endpoints. -/
theorem sourcePeriodicSegment_re_mem_Icc
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p)
    (n : ℤ) (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 ψ n) :
    z.re ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  have hle : l.re ≤ r.re :=
    re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ)).2.1 n)
  change z ∈ segment ℝ l r at hz
  obtain ⟨a,b,ha,hb,hab,rfl⟩ := hz
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  change l.re ≤ a * l.re + b * r.re ∧
    a * l.re + b * r.re ≤ r.re
  constructor
  · have haEq : a = 1-b := by linarith
    rw [haEq]
    nlinarith [mul_nonneg hb (sub_nonneg.mpr hle)]
  · have hbEq : b = 1-a := by linarith
    rw [hbEq]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hle)]

/-- Any noncentral point of a small circle lying outward of an endpoint
avoids the selected gap segment. -/
theorem sourcePeriodicSegment_not_mem_of_outward
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (z : ℂ)
    (hleft : z.re ≤ (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re ∧
      z ≠ canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n ∨
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re ≤ z.re ∧
      z ≠ canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n) :
    z ∉ sourcePeriodicSegment hp hp1 ψ n := by
  intro hz
  have hI := sourcePeriodicSegment_re_mem_Icc hp hp1 ψ n z hz
  have him := sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 ψ hreal n z hz
  have hends := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  rcases hleft with ⟨hle,hne⟩ | ⟨hle,hne⟩
  · apply hne
    apply Complex.ext
    · exact le_antisymm hle hI.1
    · exact him.trans hends.1.symm
  · apply hne
    apply Complex.ext
    · exact le_antisymm hI.2 hle
    · exact him.trans hends.2.symm

/-- Both outward endpoint semicircles, parametrized by angles between
`-π/2` and `π/2`, lie in the full root domain at small positive radii.
The negative radius on the left selects the outward half-circle. -/
theorem exists_sourceCriticalRootRatio_outerArcs_mem_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    ∃ ε : ℝ, 0 < ε ∧
      ∀ ρ ∈ Ioc 0 ε, ∀ θ ∈ Icc (-(Real.pi/2)) (Real.pi/2),
        circleMap l (-ρ) θ ∈ sourceCanonicalRootDomain hp hp1 ψ ∧
        circleMap r ρ θ ∈ sourceCanonicalRootDomain hp hp1 ψ := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let S := standardRootGapSegment
    (sourceStandardRootMidpoint hp hp1 ψ n)
    (sourceStandardRootHalfGap hp hp1 ψ n)
  obtain ⟨ε,_,hε,_,hthick,_⟩ :=
    exists_sourceCriticalRootGap_thickening_inverseOmitted_bound
      hp hp1 ψ hreal n
  have hlS : l ∈ S := by
    have hq : sourceCanonicalRootGapPoint hp hp1 ψ n (-1) ∈ S :=
      ⟨-1,by norm_num,rfl⟩
    simpa only [sourceCanonicalRootGapPoint_neg_one_eq_left] using hq
  have hrS : r ∈ S := by
    have hq : sourceCanonicalRootGapPoint hp hp1 ψ n 1 ∈ S :=
      ⟨1,by norm_num,rfl⟩
    simpa only [sourceCanonicalRootGapPoint_one_eq_right] using hq
  refine ⟨ε,hε,?_⟩
  intro ρ hρ θ hθ
  have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc hθ
  have hleftdist : dist (circleMap l (-ρ) θ) l = ρ := by
    rw [dist_eq_norm, circleMap_sub_center, norm_circleMap_zero]
    simp [abs_of_pos hρ.1]
  have hrightdist : dist (circleMap r ρ θ) r = ρ := by
    rw [dist_eq_norm, circleMap_sub_center, norm_circleMap_zero]
    exact abs_of_pos hρ.1
  have hleftOther : circleMap l (-ρ) θ ∈
      sourceStandardRootOmittedDomain hp hp1 ψ n :=
    hthick (Metric.mem_cthickening_of_dist_le _ l ε S hlS (by
      rw [hleftdist]
      exact hρ.2))
  have hrightOther : circleMap r ρ θ ∈
      sourceStandardRootOmittedDomain hp hp1 ψ n :=
    hthick (Metric.mem_cthickening_of_dist_le _ r ε S hrS (by
      rw [hrightdist]
      exact hρ.2))
  have hleftRe : (circleMap l (-ρ) θ).re ≤ l.re := by
    have heq : circleMap l (-ρ) θ = l + circleMap 0 (-ρ) θ := by
      simp [circleMap]
    rw [heq, Complex.add_re, circleMap_zero_re]
    nlinarith [mul_nonneg hρ.1.le hcos]
  have hrightRe : r.re ≤ (circleMap r ρ θ).re := by
    have heq : circleMap r ρ θ = r + circleMap 0 ρ θ := by
      simp [circleMap]
    rw [heq, Complex.add_re, circleMap_zero_re]
    nlinarith [mul_nonneg hρ.1.le hcos]
  constructor
  · intro m
    by_cases hm : m = n
    · subst m
      exact sourcePeriodicSegment_not_mem_of_outward hp hp1 ψ hreal n _
        (Or.inl ⟨hleftRe, circleMap_ne_center (neg_ne_zero.mpr hρ.1.ne')⟩)
    · exact hleftOther m hm
  · intro m
    by_cases hm : m = n
    · subst m
      exact sourcePeriodicSegment_not_mem_of_outward hp hp1 ψ hreal n _
        (Or.inr ⟨hrightRe, circleMap_ne_center hρ.1.ne'⟩)
    · exact hrightOther m hm

/-- A common small real interval strictly outside each gap endpoint
avoids every periodic cut. These are the points encountered when an
outward contour crosses the real axis. -/
theorem exists_sourceCriticalRootRatio_outerRealIntervals_mem_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    ∃ ε : ℝ, 0 < ε ∧ ∀ η ∈ Ioc 0 ε,
      l - (η:ℂ) ∈ sourceCanonicalRootDomain hp hp1 ψ ∧
      r + (η:ℂ) ∈ sourceCanonicalRootDomain hp hp1 ψ := by
  obtain ⟨ε,hε,houter⟩ :=
    exists_sourceCriticalRootRatio_outerArcs_mem_domain hp hp1 ψ hreal n
  have hθ : (0:ℝ) ∈ Icc (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [Real.pi_pos]
  refine ⟨ε,hε,?_⟩
  intro η hη
  have h := houter η hη 0 hθ
  simpa [circleMap, sub_eq_add_neg] using h

/-- At the real-axis crossing of the stadium-to-corner-circle homotopy,
the outward offset interpolates between the stadium radius and the
circle's smaller outward margin. Every such crossing avoids the cuts. -/
theorem exists_sourceCriticalRootRatio_stadiumCircleCrossings_mem_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let d := (r.re-l.re)/2
    ∃ ε : ℝ, 0 < ε ∧ ∀ ρ ∈ Ioc 0 ε, ∀ s ∈ Icc (0:ℝ) 1,
      let η := (1-s)*ρ+s*(stadiumCornerRadius d ρ-d)
      l - (η:ℂ) ∈ sourceCanonicalRootDomain hp hp1 ψ ∧
      r + (η:ℂ) ∈ sourceCanonicalRootDomain hp hp1 ψ := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let d := (r.re-l.re)/2
  obtain ⟨ε,hε,hdom⟩ :=
    exists_sourceCriticalRootRatio_outerRealIntervals_mem_domain
      hp hp1 ψ hreal n
  have hd : 0 < d := by
    change 0 < (r.re-l.re)/2
    have hgap : l.re < r.re := hopen
    exact div_pos (sub_pos.mpr hgap) (by norm_num)
  refine ⟨ε,hε,?_⟩
  intro ρ hρ s hs
  let η := (1-s)*ρ+s*(stadiumCornerRadius d ρ-d)
  have hη := stadiumCornerRadius_affineOffset_mem_Ioc hd hρ.1 hs
  have hηε : η ∈ Ioc 0 ε := ⟨hη.1,hη.2.trans hρ.2⟩
  exact hdom η hηε

/-- The full critical-root quotient has one common weighted bound on
both gap-avoiding outer endpoint arcs. -/
theorem exists_sourceCriticalRootRatio_outerArcs_weighted_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    (hopen : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n).re <
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
      ∀ ρ ∈ Ioc 0 ε, ∀ θ ∈ Icc (-(Real.pi/2)) (Real.pi/2),
        let zl := circleMap l (-ρ) θ
        let zr := circleMap r ρ θ
        zl ∈ sourceCanonicalRootDomain hp hp1 ψ ∧
        zr ∈ sourceCanonicalRootDomain hp hp1 ψ ∧
        ‖(deriv (canonicalDiscriminant hp (periodOnePotential ψ)) zl /
            sourceCanonicalRoot hp hp1 ψ zl) *
          ((Real.sqrt (((r.re-l.re)/2)*ρ) : ℝ) : ℂ)‖ ≤ M ∧
        ‖(deriv (canonicalDiscriminant hp (periodOnePotential ψ)) zr /
            sourceCanonicalRoot hp hp1 ψ zr) *
          ((Real.sqrt (((r.re-l.re)/2)*ρ) : ℝ) : ℂ)‖ ≤ M := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  obtain ⟨ε₁,hε₁,hdom⟩ :=
    exists_sourceCriticalRootRatio_outerArcs_mem_domain hp hp1 ψ hreal n
  obtain ⟨ε₂,M,hε₂,hM,hbound⟩ :=
    exists_sourceCriticalRootRatio_endpointCircle_weighted_bound
      hp hp1 ψ hreal n hopen
  let ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  refine ⟨ε,M,hε,hM,?_⟩
  intro ρ hρ θ hθ
  let zl := circleMap l (-ρ) θ
  let zr := circleMap r ρ θ
  have hρ₁ : ρ ∈ Ioc 0 ε₁ := ⟨hρ.1,hρ.2.trans (min_le_left _ _)⟩
  have hρ₂ : ρ ∈ Ioc 0 ε₂ := ⟨hρ.1,hρ.2.trans (min_le_right _ _)⟩
  obtain ⟨hldom,hrdom⟩ := hdom ρ hρ₁ θ hθ
  have hldist : ‖l-zl‖ = ρ := by
    rw [norm_sub_rev, circleMap_sub_center, norm_circleMap_zero]
    simp [abs_of_pos hρ.1]
  have hrdist : ‖r-zr‖ = ρ := by
    rw [norm_sub_rev, circleMap_sub_center, norm_circleMap_zero]
    exact abs_of_pos hρ.1
  exact ⟨hldom,hrdom,
    hbound ρ hρ₂ l (by simp [l]) zl hldom hldist,
    hbound ρ hρ₂ r (by simp [r]) zr hrdom hrdist⟩

end NLS.ZakharovShabat
