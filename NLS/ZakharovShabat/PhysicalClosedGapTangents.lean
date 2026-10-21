import NLS.ZakharovShabat.PhysicalClosedGapGeometry

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The literal squared-gap zero set from the source's real Hilbert statement. -/
def physicalClosedGapLocus (n : ℤ) : Set physicalRealSubmodule :=
  {u | (physicalPeriodicRight u.val n-physicalPeriodicLeft u.val n)^2 = 0}

/-- The kernel of the actual two-coordinate differential. -/
def physicalClosedGapTangent (n : ℤ) (u : physicalRealSubmodule) :
    Submodule ℝ physicalRealSubmodule := (fderiv ℝ (physicalGapCoordinates n) u).ker

/-- A straight line in the global analytic Birkhoff chart, returned to the physical source. -/
def physicalClosedGapCurve (u h : physicalRealSubmodule) (time : ℝ) : physicalRealSubmodule :=
  intrinsicPhysicalBirkhoffHomeomorph.symm
    (intrinsicPhysicalBirkhoffMap u + time • fderiv ℝ intrinsicPhysicalBirkhoffMap u h)

@[simp] theorem physicalClosedGapCurve_zero (u h : physicalRealSubmodule) :
    physicalClosedGapCurve u h 0 = u := by
  simp only [physicalClosedGapCurve,zero_smul,add_zero,intrinsicPhysicalBirkhoffHomeomorph_left_inv]

/-- The constructed curve is globally real analytic in time. -/
theorem physicalClosedGapCurve_analytic (u h : physicalRealSubmodule) :
    AnalyticOnNhd ℝ (physicalClosedGapCurve u h) univ := by
  intro time _
  exact (intrinsicPhysicalBirkhoffHomeomorph_analytic.2 _ (mem_univ _)).comp
    (analyticAt_const.add (analyticAt_id.smul analyticAt_const))

/-- The constructed physical curve has precisely the prescribed velocity. -/
theorem physicalClosedGapCurve_hasDerivAt_zero (u h : physicalRealSubmodule) :
    HasDerivAt (physicalClosedGapCurve u h) h 0 := by
  have hl : HasDerivAt
      (fun time : ℝ => intrinsicPhysicalBirkhoffMap u + time • fderiv ℝ intrinsicPhysicalBirkhoffMap u h)
      (fderiv ℝ intrinsicPhysicalBirkhoffMap u h) 0 := by
    simpa only [one_smul] using!
      ((hasDerivAt_id (0:ℝ)).smul_const (fderiv ℝ intrinsicPhysicalBirkhoffMap u h)).const_add
        (intrinsicPhysicalBirkhoffMap u)
  have hi : HasFDerivAt intrinsicPhysicalBirkhoffHomeomorph.symm
      (fderiv ℝ intrinsicPhysicalBirkhoffHomeomorph.symm (intrinsicPhysicalBirkhoffMap u))
      (intrinsicPhysicalBirkhoffMap u + (0:ℝ) • fderiv ℝ intrinsicPhysicalBirkhoffMap u h) := by
    simp only [zero_smul,add_zero]
    exact (intrinsicPhysicalBirkhoffHomeomorph_analytic.2 _ (mem_univ _)).differentiableAt.hasFDerivAt
  have hc := hi.comp_hasDerivAt 0 hl
  have he : (fderiv ℝ intrinsicPhysicalBirkhoffHomeomorph.symm (intrinsicPhysicalBirkhoffMap u))
      (fderiv ℝ intrinsicPhysicalBirkhoffMap u h) = h :=
    congrArg (fun L : physicalRealSubmodule →L[ℝ] physicalRealSubmodule => L h)
      (intrinsicPhysicalBirkhoffMap_fderiv_left_inverse u)
  simpa only [he] using! hc

/-- Every differential-kernel direction has an analytic curve lying entirely in the actual gap set. -/
theorem physicalClosedGapCurve_mem (n : ℤ) (u h : physicalRealSubmodule)
    (hu : u ∈ physicalClosedGapLocus n) (hh : h ∈ physicalClosedGapTangent n u) (time : ℝ) :
    physicalClosedGapCurve u h time ∈ physicalClosedGapLocus n := by
  have hu0 := (physicalGapCoordinates_zero_iff_closed n u).mpr
    ((physicalSquaredGap_zero_iff_closed n u).mp hu)
  change physicalGapEvaluation n (intrinsicPhysicalBirkhoffMap u) = 0 at hu0
  have hh0 : physicalGapEvaluation n (fderiv ℝ intrinsicPhysicalBirkhoffMap u h) = 0 := by
    change fderiv ℝ (physicalGapCoordinates n) u h = 0 at hh
    rw [physicalGapCoordinates_fderiv] at hh
    exact hh
  apply (physicalSquaredGap_zero_iff_closed n _).mpr
  apply (physicalGapCoordinates_zero_iff_closed n _).mp
  change physicalGapEvaluation n
    (intrinsicPhysicalBirkhoffMap (intrinsicPhysicalBirkhoffHomeomorph.symm _)) = 0
  rw [intrinsicPhysicalBirkhoffHomeomorph_right_inv,map_add,map_smul,hu0,hh0,smul_zero,add_zero]

/-- Every differentiable curve locally contained in the actual squared-gap zero set
has velocity in the coordinate differential kernel. -/
theorem physicalClosedGap_curve_velocity_mem (n : ℤ) (u h : physicalRealSubmodule)
    (curve : ℝ → physicalRealSubmodule) (hzero : curve 0 = u)
    (hd : HasDerivAt curve h 0)
    (hc : ∀ᶠ time in 𝓝 (0:ℝ), curve time ∈ physicalClosedGapLocus n) :
    h ∈ physicalClosedGapTangent n u := by
  have hf : HasFDerivAt (physicalGapCoordinates n) (fderiv ℝ (physicalGapCoordinates n) u)
      (curve 0) := by
    rw [hzero]
    exact (physicalGapCoordinates_analytic n u (mem_univ _)).differentiableAt.hasFDerivAt
  have he : (fun time => physicalGapCoordinates n (curve time)) =ᶠ[𝓝 (0:ℝ)] (fun _ => (0:ℝ × ℝ)) :=
    hc.mono (fun time ht => (physicalGapCoordinates_zero_iff_closed n _).mpr
      ((physicalSquaredGap_zero_iff_closed n _).mp ht))
  have hh := (hf.comp_hasDerivAt 0 hd).congr_of_eventuallyEq he.symm
  exact hh.unique (hasDerivAt_const (0:ℝ) (0:ℝ × ℝ))

/-- The full local curve tangent space is exactly the kernel of the two-coordinate differential. -/
theorem mem_physicalClosedGapTangent_iff_curve (n : ℤ) (u h : physicalRealSubmodule)
    (hu : u ∈ physicalClosedGapLocus n) :
    h ∈ physicalClosedGapTangent n u ↔
      ∃ curve : ℝ → physicalRealSubmodule, curve 0 = u ∧ HasDerivAt curve h 0 ∧
        ∀ᶠ time in 𝓝 (0:ℝ), curve time ∈ physicalClosedGapLocus n := by
  constructor
  · intro hh
    exact ⟨physicalClosedGapCurve u h,physicalClosedGapCurve_zero u h,
      physicalClosedGapCurve_hasDerivAt_zero u h,
      Filter.Eventually.of_forall (physicalClosedGapCurve_mem n u h hu hh)⟩
  · rintro ⟨curve,hzero,hd,hc⟩
    exact physicalClosedGap_curve_velocity_mem n u h curve hzero hd hc

/-- Every actual collapsed-gap tangent space has real codimension two. -/
theorem physicalClosedGapTangent_codimension_two (n : ℤ) (u : physicalRealSubmodule) :
    Module.finrank ℝ (physicalRealSubmodule ⧸ physicalClosedGapTangent n u) = 2 :=
  physicalGapCoordinates_fderiv_quotient_finrank n u

/-- The printed codimension-one value is incompatible with the actual real curve tangent space. -/
theorem physicalClosedGapTangent_codimension_ne_one (n : ℤ) (u : physicalRealSubmodule) :
    Module.finrank ℝ (physicalRealSubmodule ⧸ physicalClosedGapTangent n u) ≠ 1 := by
  rw [physicalClosedGapTangent_codimension_two]
  norm_num

/-- The zero physical potential belongs to every literal squared-gap zero set. -/
theorem zero_mem_physicalClosedGapLocus (n : ℤ) : (0:physicalRealSubmodule) ∈ physicalClosedGapLocus n := by
  apply (physicalSquaredGap_zero_iff_closed n 0).mpr
  apply (physicalGapCoordinates_zero_iff_closed n 0).mp
  simp only [physicalGapCoordinates,intrinsicPhysicalBirkhoffMap_zero,map_zero]

/-- In the real curve-tangent interpretation, the printed codimension-one claim fails already at zero. -/
theorem physicalClosedGap_printed_codimension_one_false (n : ℤ) :
    ¬ (∀ u ∈ physicalClosedGapLocus n,
      Module.finrank ℝ (physicalRealSubmodule ⧸ physicalClosedGapTangent n u) = 1) := by
  intro h
  exact physicalClosedGapTangent_codimension_ne_one n 0 (h 0 (zero_mem_physicalClosedGapLocus n))

end NLS.ZakharovShabat
