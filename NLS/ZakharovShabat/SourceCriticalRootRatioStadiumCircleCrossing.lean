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

private theorem lineMap_im_eq (z w : ℂ) (s : ℝ) :
    (AffineMap.lineMap z w s).im = (1-s)*z.im+s*w.im := by
  simp only [AffineMap.lineMap_apply_module, Complex.add_im,
    Complex.smul_im, smul_eq_mul]

private theorem lineMap_im_pos (z w : ℂ) (s : ℝ)
    (hs : s ∈ Icc (0:ℝ) 1) (hz : 0 < z.im) (hw : 0 < w.im) :
    0 < (AffineMap.lineMap z w s).im := by
  rw [lineMap_im_eq]
  by_cases hs0 : s = 0
  · subst s
    simpa using hz
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
  have hfirst : 0 ≤ (1-s)*z.im :=
    mul_nonneg (by linarith [hs.2]) hz.le
  have hsecond : 0 < s*w.im := mul_pos hspos hw
  linarith

private theorem lineMap_im_neg (z w : ℂ) (s : ℝ)
    (hs : s ∈ Icc (0:ℝ) 1) (hz : z.im < 0) (hw : w.im < 0) :
    (AffineMap.lineMap z w s).im < 0 := by
  rw [lineMap_im_eq]
  by_cases hs0 : s = 0
  · subst s
    simpa using hz
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
  have hfirst : (1-s)*z.im ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith [hs.2]) hz.le
  have hsecond : s*w.im < 0 := mul_neg_of_pos_of_neg hspos hw
  linarith

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

/-- Every intermediate point of both outer-arc affine homotopies
avoids the periodic cuts. Away from the midpoint their imaginary
coordinates have fixed nonzero signs; at the midpoint the outward
real-interval theorem applies. -/
theorem exists_sourceCriticalRootRatio_stadiumCircleOuterAffine_mem_domain
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
    ∃ ε : ℝ, 0 < ε ∧ ∀ ρ ∈ Ioc 0 ε,
      ∀ s ∈ Icc (0:ℝ) 1, ∀ u ∈ Icc (0:ℝ) 1,
      AffineMap.lineMap
        ((sourceEndpointSemicirclePath r ρ).symm.extend u)
        ((stadiumCircleRightArc c d ρ).extend u) s ∈
        sourceCanonicalRootDomain hp hp1 ψ ∧
      AffineMap.lineMap
        ((sourceLeftOuterArcPath l ρ).symm.extend u)
        ((stadiumCircleLeftArc c d ρ).extend u) s ∈
        sourceCanonicalRootDomain hp hp1 ψ := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  obtain ⟨ε,hε,hmid⟩ :=
    exists_sourceCriticalRootRatio_stadiumCircleMidpointAffine_mem_domain
      hp hp1 ψ hreal n hopen
  have hends := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have hl : l.im = 0 := hends.1
  have hr : r.im = 0 := hends.2
  have hc : c.im = 0 := by simp [c]
  have hd : 0 < d := by
    change 0 < (r.re-l.re)/2
    have hgap : l.re < r.re := hopen
    exact div_pos (sub_pos.mpr hgap) (by norm_num)
  refine ⟨ε,hε,?_⟩
  intro ρ hρ s hs u hu
  change AffineMap.lineMap
      ((sourceEndpointSemicirclePath r ρ).symm.extend u)
      ((stadiumCircleRightArc c d ρ).extend u) s ∈
        sourceCanonicalRootDomain hp hp1 ψ ∧
    AffineMap.lineMap
      ((sourceLeftOuterArcPath l ρ).symm.extend u)
      ((stadiumCircleLeftArc c d ρ).extend u) s ∈
        sourceCanonicalRootDomain hp hp1 ψ
  have hposdom (z w : ℂ) (hz : 0 < z.im) (hw : 0 < w.im) :
      AffineMap.lineMap z w s ∈ sourceCanonicalRootDomain hp hp1 ψ :=
    sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
      (ne_of_gt (lineMap_im_pos z w s hs hz hw))
  have hnegdom (z w : ℂ) (hz : z.im < 0) (hw : w.im < 0) :
      AffineMap.lineMap z w s ∈ sourceCanonicalRootDomain hp hp1 ψ :=
    sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
      (ne_of_lt (lineMap_im_neg z w s hs hz hw))
  rcases lt_trichotomy u (1/2:ℝ) with hbefore | hmiddle | hafter
  · have hrs := (sourceStadiumRightArc_im_sign r ρ u hr hρ.1 hu).1 hbefore
    have hrc := (stadiumCircleRightArc_im_sign c hc hd hρ.1 u hu).1 hbefore
    have hls := (sourceStadiumLeftArc_im_sign l ρ u hl hρ.1 hu).1 hbefore
    have hlc := (stadiumCircleLeftArc_im_sign c hc hd hρ.1 u hu).1 hbefore
    exact ⟨hposdom _ _ hrs hrc, hnegdom _ _ hls hlc⟩
  · subst u
    exact hmid ρ hρ s hs
  · have hrs := (sourceStadiumRightArc_im_sign r ρ u hr hρ.1 hu).2.2 hafter
    have hrc := (stadiumCircleRightArc_im_sign c hc hd hρ.1 u hu).2.2 hafter
    have hls := (sourceStadiumLeftArc_im_sign l ρ u hl hρ.1 hu).2.2 hafter
    have hlc := (stadiumCircleLeftArc_im_sign c hc hd hρ.1 u hu).2.2 hafter
    exact ⟨hnegdom _ _ hrs hrc, hposdom _ _ hls hlc⟩

/-- The upper and lower horizontal sides remain off the real axis
throughout their affine deformation to the matching circle arcs. -/
theorem sourceCriticalRootRatio_stadiumCircleHorizontalAffine_mem_domain
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
    ∀ ρ : ℝ, 0 < ρ → ∀ s ∈ Icc (0:ℝ) 1, ∀ u ∈ Icc (0:ℝ) 1,
      AffineMap.lineMap
        ((Path.segment (l+(ρ:ℂ)*I) (r+(ρ:ℂ)*I)).extend u)
        ((stadiumCircleUpperArc c d ρ).extend u) s ∈
        sourceCanonicalRootDomain hp hp1 ψ ∧
      AffineMap.lineMap
        ((Path.segment (r-(ρ:ℂ)*I) (l-(ρ:ℂ)*I)).extend u)
        ((stadiumCircleLowerArc c d ρ).extend u) s ∈
        sourceCanonicalRootDomain hp hp1 ψ := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  have hends := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)
    (isRealType_periodOnePotential ψ hreal) n
  have hl : l.im = 0 := hends.1
  have hr : r.im = 0 := hends.2
  have hc : c.im = 0 := by simp [c]
  have hd : 0 < d := by
    change 0 < (r.re-l.re)/2
    have hgap : l.re < r.re := hopen
    exact div_pos (sub_pos.mpr hgap) (by norm_num)
  dsimp only
  intro ρ hρ s hs u hu
  change AffineMap.lineMap
      ((Path.segment (l+(ρ:ℂ)*I) (r+(ρ:ℂ)*I)).extend u)
      ((stadiumCircleUpperArc c d ρ).extend u) s ∈
        sourceCanonicalRootDomain hp hp1 ψ ∧
    AffineMap.lineMap
      ((Path.segment (r-(ρ:ℂ)*I) (l-(ρ:ℂ)*I)).extend u)
      ((stadiumCircleLowerArc c d ρ).extend u) s ∈
        sourceCanonicalRootDomain hp hp1 ψ
  have huSeg : (Path.segment (l+(ρ:ℂ)*I) (r+(ρ:ℂ)*I)).extend u ∈
      segment ℝ (l+(ρ:ℂ)*I) (r+(ρ:ℂ)*I) := by
    rw [(Path.segment (l+(ρ:ℂ)*I) (r+(ρ:ℂ)*I)).extend_apply hu]
    rw [← Path.range_segment]
    exact ⟨⟨u,hu⟩,rfl⟩
  have hlSeg : (Path.segment (r-(ρ:ℂ)*I) (l-(ρ:ℂ)*I)).extend u ∈
      segment ℝ (r-(ρ:ℂ)*I) (l-(ρ:ℂ)*I) := by
    rw [(Path.segment (r-(ρ:ℂ)*I) (l-(ρ:ℂ)*I)).extend_apply hu]
    rw [← Path.range_segment]
    exact ⟨⟨u,hu⟩,rfl⟩
  have huIm := sourceHorizontalSegment_im_eq l r hl hr ρ _ huSeg
  have hlIm := sourceLowerHorizontalSegment_im_eq l r hl hr ρ _ hlSeg
  have hcUpper := stadiumCircleUpperArc_im_pos c hc hd hρ u hu
  have hcLower := stadiumCircleLowerArc_im_neg c hc hd hρ u hu
  constructor
  · apply sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
    exact ne_of_gt (lineMap_im_pos _ _ s hs (by rw [huIm]; exact hρ) hcUpper)
  · apply sourceCanonicalRootDomain_of_im_ne_zero hp hp1 ψ hreal _
    exact ne_of_lt (lineMap_im_neg _ _ s hs (by rw [hlIm]; linarith) hcLower)

/-- All four matching pieces of the stadium-to-corner-circle affine
deformation lie in the canonical-root domain at one common small
stadium radius. -/
theorem exists_sourceCriticalRootRatio_stadiumCircleAffine_mem_domain
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
    ∃ ε : ℝ, 0 < ε ∧ ∀ ρ ∈ Ioc 0 ε,
      ∀ s ∈ Icc (0:ℝ) 1, ∀ u ∈ Icc (0:ℝ) 1,
      AffineMap.lineMap
        ((Path.segment (l+(ρ:ℂ)*I) (r+(ρ:ℂ)*I)).extend u)
        ((stadiumCircleUpperArc c d ρ).extend u) s ∈
        sourceCanonicalRootDomain hp hp1 ψ ∧
      AffineMap.lineMap
        ((sourceEndpointSemicirclePath r ρ).symm.extend u)
        ((stadiumCircleRightArc c d ρ).extend u) s ∈
        sourceCanonicalRootDomain hp hp1 ψ ∧
      AffineMap.lineMap
        ((Path.segment (r-(ρ:ℂ)*I) (l-(ρ:ℂ)*I)).extend u)
        ((stadiumCircleLowerArc c d ρ).extend u) s ∈
        sourceCanonicalRootDomain hp hp1 ψ ∧
      AffineMap.lineMap
        ((sourceLeftOuterArcPath l ρ).symm.extend u)
        ((stadiumCircleLeftArc c d ρ).extend u) s ∈
        sourceCanonicalRootDomain hp hp1 ψ := by
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2 : ℝ) : ℂ)
  let d : ℝ := (r.re-l.re)/2
  obtain ⟨ε,hε,houter⟩ :=
    exists_sourceCriticalRootRatio_stadiumCircleOuterAffine_mem_domain
      hp hp1 ψ hreal n hopen
  have hhorizontal :=
    sourceCriticalRootRatio_stadiumCircleHorizontalAffine_mem_domain
      hp hp1 ψ hreal n hopen
  refine ⟨ε,hε,?_⟩
  intro ρ hρ s hs u hu
  have hO := houter ρ hρ s hs u hu
  have hH := hhorizontal ρ hρ.1 s hs u hu
  exact ⟨hH.1,hO.1,hH.2,hO.2⟩

end NLS.ZakharovShabat
