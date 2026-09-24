import NLS.ZakharovShabat.SourceCriticalRootRatioStadiumHomotopy
import NLS.ZakharovShabat.SourceCriticalRootRatioEnclosingCircle

/-!
# Midpoint-centered circles around real periodic gaps

A circle centered at the midpoint of a real gap and extending a small
distance past both endpoints meets the real axis only at the two
outward endpoint points. The existing outer-arc domain result controls
those points; every other point of the circle has nonzero imaginary
part and avoids all real-type periodic cuts.
-/

noncomputable section
open Set Metric Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A real point on a circle with real center is one of its two
horizontal extremes. -/
theorem sourceRealPoint_mem_sphere_eq_horizontal_extreme
    (c z : ℂ) (R : ℝ) (hc : c.im = 0) (hz : z.im = 0)
    (hsphere : z ∈ sphere c R) :
    z = c + (R:ℂ) ∨ z = c - (R:ℂ) := by
  have hnorm : ‖z-c‖ = R := by
    simpa only [mem_sphere, dist_eq_norm] using hsphere
  have hsq : (z.re-c.re)^2 = R^2 := by
    calc
      (z.re-c.re)^2 = Complex.normSq (z-c) := by
        simp [Complex.normSq_apply, Complex.sub_re,
          Complex.sub_im, hc, hz, pow_two]
      _ = ‖z-c‖^2 := (Complex.sq_norm (z-c)).symm
      _ = R^2 := by rw [hnorm]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with hright | hleft
  · left
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re]
      linarith
    · simp [hc, hz]
  · right
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.ofReal_re]
      linarith
    · simp [hc, hz]

/-- Distance between two points on the real axis is the absolute
difference of their real coordinates. -/
theorem sourceRealPoints_dist_eq_abs_re_sub
    (z c : ℂ) (hz : z.im = 0) (hc : c.im = 0) :
    dist z c = |z.re-c.re| := by
  have hz' : z = (z.re:ℂ) := by
    apply Complex.ext <;> simp [hz]
  have hc' : c = (c.re:ℂ) := by
    apply Complex.ext <;> simp [hc]
  rw [hz',hc']
  simp [dist_eq_norm, ← Complex.ofReal_sub]

/-- A positive margin beyond both endpoints makes the midpoint
circle enclose the full real periodic gap. -/
theorem sourcePeriodicSegment_subset_midpoint_ball
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (ρ : ℝ) (hρ : 0 < ρ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    sourcePeriodicSegment hp hp1 ψ n ⊆ ball c (d+ρ) := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  dsimp only
  intro z hz
  have hI := sourcePeriodicSegment_re_mem_Icc hp hp1 ψ n z hz
  have him := sourcePeriodicSegment_im_eq_zero_of_realType hp hp1 ψ hreal n z hz
  have hc : c.im = 0 := by simp [c]
  have hdist : dist z c = |z.re-c.re| :=
    sourceRealPoints_dist_eq_abs_re_sub z c him hc
  have hbounds : -d ≤ z.re-c.re ∧ z.re-c.re ≤ d := by
    dsimp [c,d]
    constructor <;> linarith [hI.1,hI.2]
  rw [mem_ball, hdist]
  change |z.re-c.re| < d+ρ
  exact lt_of_le_of_lt (abs_le.mpr hbounds) (by linarith)

/-- Sufficiently small midpoint-centered circles around a real-type
gap lie entirely in the full canonical-root domain. -/
theorem exists_sourceCriticalRootRatio_midpointCircle_mem_rootDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∃ ε : ℝ, 0 < ε ∧ ∀ ρ ∈ Ioc 0 ε,
      0 < d+ρ ∧
      sourcePeriodicSegment hp hp1 ψ n ⊆ ball c (d+ρ) ∧
      sphere c (d+ρ) ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  obtain ⟨ε,hε,hdom⟩ :=
    exists_sourceCriticalRootRatio_outerArcs_mem_domain hp hp1 ψ hreal n
  have hends := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have hl : l.im = 0 := hends.1
  have hr : r.im = 0 := hends.2
  have hc : c.im = 0 := by simp [c]
  have hle : l.re ≤ r.re :=
    re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ)).2.1 n)
  have hd : 0 ≤ d := by dsimp [d]; linarith
  have hθ : (0:ℝ) ∈ Icc (-(Real.pi/2)) (Real.pi/2) := by
    constructor <;> linarith [Real.pi_pos]
  refine ⟨ε,hε,?_⟩
  intro ρ hρ
  refine ⟨by linarith [hρ.1], ?_, ?_⟩
  · exact sourcePeriodicSegment_subset_midpoint_ball hp hp1 ψ hreal n ρ hρ.1
  intro z hz
  by_cases hzIm : z.im = 0
  · rcases sourceRealPoint_mem_sphere_eq_horizontal_extreme
      c z (d+ρ) hc hzIm hz with hright | hleft
    · have hzright : z = r + (ρ:ℂ) := by
        apply Complex.ext
        · rw [hright]
          simp only [Complex.add_re, Complex.ofReal_re]
          dsimp [c,d]
          ring
        · simp [hright, hc, hr]
      rw [hzright]
      have h := (hdom ρ hρ 0 hθ).2
      simpa [circleMap, r] using h
    · have hzleft : z = l - (ρ:ℂ) := by
        apply Complex.ext
        · rw [hleft]
          simp only [Complex.sub_re, Complex.ofReal_re]
          dsimp [c,d]
          ring
        · simp [hleft, hc, hl]
      rw [hzleft]
      have h := (hdom ρ hρ 0 hθ).1
      simpa [circleMap, l, sub_eq_add_neg] using h
  · exact sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal z hzIm

end NLS.ZakharovShabat
