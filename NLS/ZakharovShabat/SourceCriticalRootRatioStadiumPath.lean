import NLS.ZakharovShabat.SourceCriticalRootRatioOuterArcIntegral
import Mathlib.Analysis.Convex.PathConnected

/-!
# A closed shrinking stadium around a real periodic gap

Two horizontal translates of a real gap connect to the outward endpoint
semicircles. Their concatenation is a closed path, and sufficiently
small positive radii keep every point of this path in the full
canonical-root domain.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The circular arc traversed from its negative imaginary endpoint
to its positive imaginary endpoint. A negative signed radius puts the
arc on the left of its center. -/
def sourceEndpointSemicirclePath (c : ℂ) (R : ℝ) :
    Path (c-(R:ℂ)*I) (c+(R:ℂ)*I) :=
  Path.ofLine
    (f := fun t : ℝ => circleMap c R (-(Real.pi/2)+Real.pi*t))
    (by fun_prop)
    (by simpa [neg_div] using circleMap_neg_pi_div_two c R)
    (by
      have hangle : -(Real.pi/2)+Real.pi*1 = Real.pi/2 := by ring
      simpa only [hangle] using circleMap_pi_div_two c R)

/-- Recast the negative-radius arc with the actual vertical endpoints
of the left side of the stadium. -/
def sourceLeftOuterArcPath (l : ℂ) (ρ : ℝ) :
    Path (l+(ρ:ℂ)*I) (l-(ρ:ℂ)*I) :=
  (sourceEndpointSemicirclePath l (-ρ)).cast
    (by push_cast; ring) (by push_cast; ring)

/-- A closed stadium path around the segment from `l` to `r`. It runs
right along the upper side, down around the right endpoint, left along
the lower side, and up around the left endpoint. -/
def sourceGapStadiumPath (l r : ℂ) (ρ : ℝ) :
    Path (l+(ρ:ℂ)*I) (l+(ρ:ℂ)*I) :=
  let upper : Path (l+(ρ:ℂ)*I) (r+(ρ:ℂ)*I) :=
    Path.segment (l+(ρ:ℂ)*I) (r+(ρ:ℂ)*I)
  let right : Path (r+(ρ:ℂ)*I) (r-(ρ:ℂ)*I) :=
    (sourceEndpointSemicirclePath r ρ).symm
  let lower : Path (r-(ρ:ℂ)*I) (l-(ρ:ℂ)*I) :=
    Path.segment (r-(ρ:ℂ)*I) (l-(ρ:ℂ)*I)
  let left : Path (l-(ρ:ℂ)*I) (l+(ρ:ℂ)*I) :=
    (sourceLeftOuterArcPath l ρ).symm
  ((upper.trans right).trans lower).trans left

/-- The reversed endpoint semicircle, as used in the stadium, has
the clockwise angle `π/2-πt`. -/
theorem sourceEndpointSemicirclePath_symm_apply
    (c : ℂ) (R t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    ((sourceEndpointSemicirclePath c R).symm).extend t =
      circleMap c R (Real.pi/2-Real.pi*t) := by
  rw [Path.extend_symm_apply]
  have ht' : 1-t ∈ Icc (0:ℝ) 1 := by
    constructor <;> linarith [ht.1,ht.2]
  rw [(sourceEndpointSemicirclePath c R).extend_apply ht']
  change circleMap c R (-(Real.pi/2)+Real.pi*(1-t)) = _
  congr 1
  ring

/-- The stadium's right semicircle crosses the real axis at its
outward midpoint. -/
theorem sourceStadiumRightArc_midpoint (r : ℂ) (ρ : ℝ) :
    ((sourceEndpointSemicirclePath r ρ).symm).extend (1/2:ℝ) =
      r + (ρ:ℂ) := by
  have ht : (1/2:ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
  rw [sourceEndpointSemicirclePath_symm_apply r ρ _ ht]
  have hangle : Real.pi/2-Real.pi*(1/2:ℝ) = 0 := by ring
  rw [hangle]
  simp [circleMap]

/-- The stadium's left semicircle crosses the real axis at its
outward midpoint. -/
theorem sourceStadiumLeftArc_midpoint (l : ℂ) (ρ : ℝ) :
    ((sourceLeftOuterArcPath l ρ).symm).extend (1/2:ℝ) =
      l - (ρ:ℂ) := by
  have ht : (1/2:ℝ) ∈ Icc (0:ℝ) 1 := by norm_num
  change ((sourceEndpointSemicirclePath l (-ρ)).symm).extend (1/2:ℝ) = _
  rw [sourceEndpointSemicirclePath_symm_apply l (-ρ) _ ht]
  have hangle : Real.pi/2-Real.pi*(1/2:ℝ) = 0 := by ring
  rw [hangle]
  simp [circleMap, sub_eq_add_neg]

/-- Imaginary coordinate of a reversed endpoint semicircle about a
real center. -/
theorem sourceEndpointSemicirclePath_symm_im
    (c : ℂ) (R t : ℝ) (hc : c.im = 0)
    (ht : t ∈ Icc (0:ℝ) 1) :
    (((sourceEndpointSemicirclePath c R).symm).extend t).im =
      R * Real.sin (Real.pi/2-Real.pi*t) := by
  rw [sourceEndpointSemicirclePath_symm_apply c R t ht]
  have h := congrArg Complex.im
    (circleMap_sub_center c R (Real.pi/2-Real.pi*t))
  simpa only [Complex.sub_im, hc, sub_zero, circleMap_zero_im] using h

/-- The stadium's right arc stays above the real axis before its
midpoint and below it afterward. -/
theorem sourceStadiumRightArc_im_sign
    (r : ℂ) (ρ t : ℝ) (hr : r.im = 0) (hρ : 0 < ρ)
    (ht : t ∈ Icc (0:ℝ) 1) :
    (t < 1/2 → 0 < (((sourceEndpointSemicirclePath r ρ).symm).extend t).im) ∧
    (t = 1/2 → (((sourceEndpointSemicirclePath r ρ).symm).extend t).im = 0) ∧
    (1/2 < t → (((sourceEndpointSemicirclePath r ρ).symm).extend t).im < 0) := by
  rw [sourceEndpointSemicirclePath_symm_im r ρ t hr ht]
  have hπt0 : 0 ≤ Real.pi*t := mul_nonneg Real.pi_pos.le ht.1
  have hπt1 : Real.pi*t ≤ Real.pi := by
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr ht.2)]
  refine ⟨?_, ?_, ?_⟩
  · intro hhalf
    have hπthalf : Real.pi*t < Real.pi/2 := by
      nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hhalf)]
    have hθ : Real.pi/2-Real.pi*t ∈ Ioo (0:ℝ) Real.pi := by
      constructor <;> linarith [Real.pi_pos]
    exact mul_pos hρ (Real.sin_pos_of_mem_Ioo hθ)
  · intro hhalf
    subst t
    have hangle : Real.pi/2-Real.pi*(1/2:ℝ) = 0 := by ring
    rw [hangle, Real.sin_zero, mul_zero]
  · intro hhalf
    have hπthalf : Real.pi/2 < Real.pi*t := by
      nlinarith [mul_pos Real.pi_pos (sub_pos.mpr hhalf)]
    have hθ : -Real.pi < Real.pi/2-Real.pi*t := by
      linarith [Real.pi_pos]
    exact mul_neg_of_pos_of_neg hρ
      (Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) hθ)

/-- The left arc has the opposite imaginary signs from the right arc. -/
theorem sourceStadiumLeftArc_im_sign
    (l : ℂ) (ρ t : ℝ) (hl : l.im = 0) (hρ : 0 < ρ)
    (ht : t ∈ Icc (0:ℝ) 1) :
    (t < 1/2 → (((sourceLeftOuterArcPath l ρ).symm).extend t).im < 0) ∧
    (t = 1/2 → (((sourceLeftOuterArcPath l ρ).symm).extend t).im = 0) ∧
    (1/2 < t → 0 < (((sourceLeftOuterArcPath l ρ).symm).extend t).im) := by
  have him : (((sourceLeftOuterArcPath l ρ).symm).extend t).im =
      -ρ * Real.sin (Real.pi/2-Real.pi*t) := by
    change (((sourceEndpointSemicirclePath l (-ρ)).symm).extend t).im = _
    exact sourceEndpointSemicirclePath_symm_im l (-ρ) t hl ht
  have hright := sourceStadiumRightArc_im_sign l ρ t hl hρ ht
  rw [him]
  have hrightIm := sourceEndpointSemicirclePath_symm_im l ρ t hl ht
  rw [hrightIm] at hright
  constructor
  · intro h
    have hh := hright.1 h
    nlinarith
  constructor
  · intro h
    have hh := hright.2.1 h
    nlinarith
  · intro h
    have hh := hright.2.2 h
    nlinarith

/-- A point with nonzero imaginary part avoids every real-type source
periodic gap segment. -/
theorem sourceCanonicalRootDomain_of_im_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (z : ℂ) (hz : z.im ≠ 0) :
    z ∈ sourceCanonicalRootDomain hp hp1 ψ := by
  intro m hm
  exact hz (sourcePeriodicSegment_im_eq_zero_of_realType
    hp hp1 ψ hreal m z hm)

/-- Every point of a horizontal segment between vertically shifted
real endpoints has the same imaginary coordinate. -/
theorem sourceHorizontalSegment_im_eq
    (l r : ℂ) (hl : l.im = 0) (hr : r.im = 0)
    (ρ : ℝ) (z : ℂ)
    (hz : z ∈ segment ℝ (l+(ρ:ℂ)*I) (r+(ρ:ℂ)*I)) :
    z.im = ρ := by
  obtain ⟨a,b,ha,hb,hab,rfl⟩ := hz
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
  simp [hl,hr]
  calc
    a * ρ + b * ρ = (a+b)*ρ := by ring
    _ = ρ := by rw [hab]; ring

/-- The same imaginary-coordinate statement for the lower horizontal
segment, traversed from right to left. -/
theorem sourceLowerHorizontalSegment_im_eq
    (l r : ℂ) (hl : l.im = 0) (hr : r.im = 0)
    (ρ : ℝ) (z : ℂ)
    (hz : z ∈ segment ℝ (r-(ρ:ℂ)*I) (l-(ρ:ℂ)*I)) :
    z.im = -ρ := by
  obtain ⟨a,b,ha,hb,hab,rfl⟩ := hz
  simp only [Complex.add_im, Complex.sub_im, Complex.smul_im, smul_eq_mul]
  simp [hl,hr]
  calc
    -(a * ρ) + -(b * ρ) = (a+b)*-ρ := by ring
    _ = -ρ := by rw [hab]; ring

/-- If a circle map avoids the cuts on its outward half, its path
version has the same gap-avoidance property. -/
theorem sourceEndpointSemicirclePath_range_subset
    (c : ℂ) (R : ℝ) (D : Set ℂ)
    (hD : ∀ θ ∈ Icc (-(Real.pi/2)) (Real.pi/2),
      circleMap c R θ ∈ D) :
    range (sourceEndpointSemicirclePath c R) ⊆ D := by
  intro z hz
  obtain ⟨t,rfl⟩ := hz
  change circleMap c R (-(Real.pi/2)+Real.pi*(t:ℝ)) ∈ D
  have ht : (t:ℝ) ∈ Icc (0:ℝ) 1 := t.property
  have hmul0 : 0 ≤ Real.pi*(t:ℝ) :=
    mul_nonneg Real.pi_pos.le ht.1
  have hmul1 : Real.pi*(t:ℝ) ≤ Real.pi := by
    simpa using (mul_le_mul_of_nonneg_left ht.2 Real.pi_pos.le)
  apply hD
  constructor <;> linarith

/-- For sufficiently small positive radii, the entire closed stadium
around a real-type periodic gap avoids all periodic cuts. -/
theorem exists_sourceGapStadiumPath_range_subset_rootDomain
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    ∃ ε : ℝ, 0 < ε ∧ ∀ ρ ∈ Ioc 0 ε,
      range (sourceGapStadiumPath l r ρ) ⊆
        sourceCanonicalRootDomain hp hp1 ψ := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  have hends := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have hl : l.im = 0 := hends.1
  have hr : r.im = 0 := hends.2
  obtain ⟨ε,hε,hdom⟩ :=
    exists_sourceCriticalRootRatio_outerArcs_mem_domain hp hp1 ψ hreal n
  refine ⟨ε,hε,?_⟩
  intro ρ hρ
  let upper : Path (l+(ρ:ℂ)*I) (r+(ρ:ℂ)*I) :=
    Path.segment (l+(ρ:ℂ)*I) (r+(ρ:ℂ)*I)
  let right : Path (r+(ρ:ℂ)*I) (r-(ρ:ℂ)*I) :=
    (sourceEndpointSemicirclePath r ρ).symm
  let lower : Path (r-(ρ:ℂ)*I) (l-(ρ:ℂ)*I) :=
    Path.segment (r-(ρ:ℂ)*I) (l-(ρ:ℂ)*I)
  let left : Path (l-(ρ:ℂ)*I) (l+(ρ:ℂ)*I) :=
    (sourceLeftOuterArcPath l ρ).symm
  have hupper : range upper ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    rw [show range upper = segment ℝ (l+(ρ:ℂ)*I) (r+(ρ:ℂ)*I) from
      Path.range_segment _ _]
    intro z hz
    apply sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal z
    rw [sourceHorizontalSegment_im_eq l r hl hr ρ z hz]
    exact hρ.1.ne'
  have hlower : range lower ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    rw [show range lower = segment ℝ (r-(ρ:ℂ)*I) (l-(ρ:ℂ)*I) from
      Path.range_segment _ _]
    intro z hz
    apply sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal z
    rw [sourceLowerHorizontalSegment_im_eq l r hl hr ρ z hz]
    exact neg_ne_zero.mpr hρ.1.ne'
  have hright : range right ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    rw [show range right = range (sourceEndpointSemicirclePath r ρ) from
      Path.symm_range _]
    exact sourceEndpointSemicirclePath_range_subset r ρ _
      (fun θ hθ => (hdom ρ hρ θ hθ).2)
  have hleft : range left ⊆ sourceCanonicalRootDomain hp hp1 ψ := by
    rw [show range left = range (sourceLeftOuterArcPath l ρ) from
      Path.symm_range _]
    have hcast : range (sourceLeftOuterArcPath l ρ) =
        range (sourceEndpointSemicirclePath l (-ρ)) := by
      rfl
    rw [hcast]
    exact sourceEndpointSemicirclePath_range_subset l (-ρ) _
      (fun θ hθ => (hdom ρ hρ θ hθ).1)
  change range (((upper.trans right).trans lower).trans left) ⊆
    sourceCanonicalRootDomain hp hp1 ψ
  rw [Path.trans_range, Path.trans_range, Path.trans_range]
  exact union_subset (union_subset (union_subset hupper hright) hlower) hleft

end NLS.ZakharovShabat
