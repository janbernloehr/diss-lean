import NLS.ZakharovShabat.PhysicalAngularValues

/-! # The Birkhoff map from intrinsic physical integrals

Literal physical action and angle integrals define the coordinates.
Their l2 membership and equality with every original family give the full
map, global analytic inverse, and exact Hilbert norm preservation.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal Classical unitInterval
namespace NLS.ZakharovShabat

/-- The action chosen as a literal physical contour integral. -/
def intrinsicPhysicalAction (n : ℤ) (u : physicalRealSubmodule) : ℂ :=
  let C := Classical.choice (exists_physicalSpectralCircle u n)
  (Real.pi:ℂ)⁻¹ * ∮ z in C((C.center:ℂ),C.radius),
    z*deriv (l2Discriminant u.val) z/physicalCanonicalProductRoot u.val z

/-- The literal physical action equals the established indexed action. -/
theorem intrinsicPhysicalAction_eq_indexed (n : ℤ) (u : physicalRealSubmodule) :
    intrinsicPhysicalAction n u = physicalIndexedAction n u.val :=
  (Classical.choice (exists_physicalSpectralCircle u n)).action.symm

/-- The real cosine coordinate with the nonnegative action square root. -/
def intrinsicPhysicalX (u : physicalRealSubmodule) (n : ℤ) : ℝ :=
  Real.sqrt (2*(intrinsicPhysicalAction n u).re)*Real.cos (physicalTheta n u).re

/-- The real sine coordinate with the positive sine orientation. -/
def intrinsicPhysicalY (u : physicalRealSubmodule) (n : ℤ) : ℝ :=
  Real.sqrt (2*(intrinsicPhysicalAction n u).re)*Real.sin (physicalTheta n u).re

/-- The independently defined coordinates belong to the physical Hilbert target. -/
theorem intrinsicPhysical_coordinates_memlp (u : physicalRealSubmodule) :
    Memℓp (intrinsicPhysicalX u) 2 ∧ Memℓp (intrinsicPhysicalY u) 2 := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  let A := D.toSourceSection14OriginalData
  have hx : intrinsicPhysicalX u = ((A.physicalRealActionAngleHomeomorph u).fst : ℤ → ℝ) := by
    funext n
    simpa only [intrinsicPhysicalX,intrinsicPhysicalAction_eq_indexed] using
      (A.physicalRealActionAngleHomeomorph_intrinsic_formula u n).1.symm
  have hy : intrinsicPhysicalY u = ((A.physicalRealActionAngleHomeomorph u).snd : ℤ → ℝ) := by
    funext n
    simpa only [intrinsicPhysicalY,intrinsicPhysicalAction_eq_indexed] using
      (A.physicalRealActionAngleHomeomorph_intrinsic_formula u n).2.symm
  rw [hx,hy]
  exact ⟨(A.physicalRealActionAngleHomeomorph u).fst.property,(A.physicalRealActionAngleHomeomorph u).snd.property⟩

/-- The full map is constructed directly from intrinsic physical action and angle integrals. -/
def intrinsicPhysicalBirkhoffMap (u : physicalRealSubmodule) : PhysicalRealBirkhoffTarget :=
  WithLp.toLp 2 (⟨intrinsicPhysicalX u,(intrinsicPhysical_coordinates_memlp u).1⟩,
    ⟨intrinsicPhysicalY u,(intrinsicPhysical_coordinates_memlp u).2⟩)

namespace SourceSection14OriginalData
variable {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  (D : SourceSection14OriginalData (by simp) (by norm_num) W₀ W V s)
include D

/-- Exact equality of the independently constructed physical map with every original family. -/
theorem intrinsicPhysicalBirkhoffMap_eq : intrinsicPhysicalBirkhoffMap = D.physicalRealActionAngleHomeomorph := by
  funext u
  apply WithLp.ofLp_injective
  apply Prod.ext
  · apply Subtype.ext
    funext n
    simpa only [intrinsicPhysicalBirkhoffMap,intrinsicPhysicalX,intrinsicPhysicalAction_eq_indexed,WithLp.fst] using
      (D.physicalRealActionAngleHomeomorph_intrinsic_formula u n).1.symm
  · apply Subtype.ext
    funext n
    simpa only [intrinsicPhysicalBirkhoffMap,intrinsicPhysicalY,intrinsicPhysicalAction_eq_indexed,WithLp.snd] using
      (D.physicalRealActionAngleHomeomorph_intrinsic_formula u n).2.symm

end SourceSection14OriginalData

/-- The intrinsic physical map is analytic and has a global analytic inverse in the Hilbert norms. -/
theorem intrinsicPhysicalBirkhoffMap_global_inverse :
    ∃ e : physicalRealSubmodule ≃ₜ PhysicalRealBirkhoffTarget,
      (e : physicalRealSubmodule → PhysicalRealBirkhoffTarget) = intrinsicPhysicalBirkhoffMap ∧
      AnalyticOnNhd ℝ e univ ∧ AnalyticOnNhd ℝ e.symm univ ∧ (∀ u, ‖e u‖ = ‖u‖) := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  let A := D.toSourceSection14OriginalData
  exact ⟨A.physicalRealActionAngleHomeomorph,A.intrinsicPhysicalBirkhoffMap_eq.symm,
    A.physicalRealActionAngleHomeomorph_analytic.1,A.physicalRealActionAngleHomeomorph_analytic.2,
    A.physicalRealActionAngleHomeomorph_norm⟩

/-- The intrinsic map sends the zero potential, with all gaps collapsed, to the zero sequence. -/
theorem intrinsicPhysicalBirkhoffMap_zero : intrinsicPhysicalBirkhoffMap 0 = 0 := by
  obtain ⟨e,he,_,_,hn⟩ := intrinsicPhysicalBirkhoffMap_global_inverse
  apply norm_eq_zero.mp
  rw [← he,hn,norm_zero]

end NLS.ZakharovShabat
