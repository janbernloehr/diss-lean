import NLS.ZakharovShabat.SourceCriticalRootRatioMidpointCircle
import NLS.ComplexAnalysis.StadiumCircleCorners

/-!
# Real crossings in the stadium-to-circle deformation

At their common midpoint parameter, the two outer stadium semicircles
and the matching corner-circle arcs are real. Their affine homotopies
run through precisely the short real intervals outside the gap
endpoints, where the canonical root is defined.
-/

noncomputable section
open Set Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The affine interpolation of the right crossing has an explicit
positive outward offset from the right gap endpoint. -/
theorem sourceStadiumCircleRight_midpoint_affine_eq
    (l r : ℂ) (ρ s : ℝ) (hr : r.im = 0)
    (hd : 0 < (r.re-l.re)/2) (hρ : 0 < ρ) :
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    AffineMap.lineMap
      ((sourceEndpointSemicirclePath r ρ).symm.extend (1/2:ℝ))
      ((stadiumCircleRightArc c d ρ).extend (1/2:ℝ)) s =
      r + (((1-s)*ρ+s*(stadiumCornerRadius d ρ-d):ℝ):ℂ) := by
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  have hcircle := stadiumCircleRightArc_midpoint c (d := d) (ρ := ρ) hd hρ
  have hstadium := sourceStadiumRightArc_midpoint r ρ
  have hcenter : c + (stadiumCornerRadius d ρ : ℂ) =
      r + ((stadiumCornerRadius d ρ-d:ℝ):ℂ) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re]
      dsimp [c,d]
      ring
    · simp [c,hr]
  change AffineMap.lineMap
    ((sourceEndpointSemicirclePath r ρ).symm.extend (1/2:ℝ))
    ((stadiumCircleRightArc c d ρ).extend (1/2:ℝ)) s =
    r + (((1-s)*ρ+s*(stadiumCornerRadius d ρ-d):ℝ):ℂ)
  rw [hcircle, hstadium, hcenter]
  simp only [AffineMap.lineMap_apply_module, Complex.real_smul]
  push_cast
  ring

/-- The left crossing follows the matching short outward interval. -/
theorem sourceStadiumCircleLeft_midpoint_affine_eq
    (l r : ℂ) (ρ s : ℝ) (hl : l.im = 0)
    (hd : 0 < (r.re-l.re)/2) (hρ : 0 < ρ) :
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    AffineMap.lineMap
      ((sourceLeftOuterArcPath l ρ).symm.extend (1/2:ℝ))
      ((stadiumCircleLeftArc c d ρ).extend (1/2:ℝ)) s =
      l - (((1-s)*ρ+s*(stadiumCornerRadius d ρ-d):ℝ):ℂ) := by
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  have hcircle := stadiumCircleLeftArc_midpoint c (d := d) (ρ := ρ) hd hρ
  have hstadium := sourceStadiumLeftArc_midpoint l ρ
  have hcenter : c - (stadiumCornerRadius d ρ : ℂ) =
      l - ((stadiumCornerRadius d ρ-d:ℝ):ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.ofReal_re]
      dsimp [c,d]
      ring
    · simp [c,hl]
  change AffineMap.lineMap
    ((sourceLeftOuterArcPath l ρ).symm.extend (1/2:ℝ))
    ((stadiumCircleLeftArc c d ρ).extend (1/2:ℝ)) s =
    l - (((1-s)*ρ+s*(stadiumCornerRadius d ρ-d):ℝ):ℂ)
  rw [hcircle, hstadium, hcenter]
  simp only [AffineMap.lineMap_apply_module, Complex.real_smul]
  push_cast
  ring

/-- Both real-axis crossings of the actual affine stadium-to-circle
deformation remain in the canonical-root domain. -/
theorem exists_sourceCriticalRootRatio_stadiumCircleMidpointAffine_mem_domain
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
    let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
    let d : ℝ := (r.re-l.re)/2
    ∃ ε : ℝ, 0 < ε ∧ ∀ ρ ∈ Ioc 0 ε, ∀ s ∈ Icc (0:ℝ) 1,
      AffineMap.lineMap
        ((sourceEndpointSemicirclePath r ρ).symm.extend (1/2:ℝ))
        ((stadiumCircleRightArc c d ρ).extend (1/2:ℝ)) s ∈
        sourceCanonicalRootDomain hp hp1 ψ ∧
      AffineMap.lineMap
        ((sourceLeftOuterArcPath l ρ).symm.extend (1/2:ℝ))
        ((stadiumCircleLeftArc c d ρ).extend (1/2:ℝ)) s ∈
        sourceCanonicalRootDomain hp hp1 ψ := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  obtain ⟨ε,hε,hcross⟩ :=
    exists_sourceCriticalRootRatio_stadiumCircleCrossings_mem_domain
      hp hp1 ψ hreal n hopen
  have hends := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have hl : l.im = 0 := hends.1
  have hr : r.im = 0 := hends.2
  have hd : 0 < d := by
    change 0 < (r.re-l.re)/2
    have hgap : l.re < r.re := hopen
    exact div_pos (sub_pos.mpr hgap) (by norm_num)
  refine ⟨ε,hε,?_⟩
  intro ρ hρ s hs
  have hrealCross := hcross ρ hρ s hs
  have hright := sourceStadiumCircleRight_midpoint_affine_eq
    l r ρ s hr hd hρ.1
  have hleft := sourceStadiumCircleLeft_midpoint_affine_eq
    l r ρ s hl hd hρ.1
  change AffineMap.lineMap
      ((sourceEndpointSemicirclePath r ρ).symm.extend (1/2:ℝ))
      ((stadiumCircleRightArc c d ρ).extend (1/2:ℝ)) s ∈
        sourceCanonicalRootDomain hp hp1 ψ ∧
    AffineMap.lineMap
      ((sourceLeftOuterArcPath l ρ).symm.extend (1/2:ℝ))
      ((stadiumCircleLeftArc c d ρ).extend (1/2:ℝ)) s ∈
        sourceCanonicalRootDomain hp hp1 ψ
  rw [hright, hleft]
  exact ⟨hrealCross.2, hrealCross.1⟩

end NLS.ZakharovShabat
