import NLS.ZakharovShabat.PhysicalCanonicalRoot

/-! # Physical isolating circles and action integrals

The circle geometry refers only to intrinsic physical gaps. Every real L2
input supplies such circles, their spheres are nonsingular, and their
literal integrals compute the existing physical indexed actions.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- A real-centered circle isolating one physical gap horizontally from every other gap. -/
structure PhysicalSpectralCircle (u : IntervalPairL2) (n : ℤ) where
  center : ℝ
  radius : ℝ
  radius_pos : 0 < radius
  gap : physicalPeriodicSegment u n ⊆ ball (center:ℂ) radius
  other : ∀ m : ℤ, m ≠ n → ∀ w ∈ physicalPeriodicSegment u m,
    w.re < center-radius ∨ center+radius < w.re

/-- The physical geometry supplies a source period circle without changing its center or radius. -/
def PhysicalSpectralCircle.toSource {u : IntervalPairL2} {n : ℤ}
    (C : PhysicalSpectralCircle u n) :
    SourceCriticalRootPeriodCircle (by simp) (by norm_num) (sourcePhysicalL2Equiv.symm u) n where
  center := C.center
  radius := C.radius
  radius_pos := C.radius_pos
  gap := by simpa only [physicalPeriodicSegment_eq_source] using C.gap
  other := by simpa only [physicalPeriodicSegment_eq_source] using C.other

/-- A source period circle gives the same physical geometry. -/
def PhysicalSpectralCircle.ofSource {u : IntervalPairL2} {n : ℤ}
    (C : SourceCriticalRootPeriodCircle (by simp) (by norm_num) (sourcePhysicalL2Equiv.symm u) n) :
    PhysicalSpectralCircle u n where
  center := C.center
  radius := C.radius
  radius_pos := C.radius_pos
  gap := by simpa only [physicalPeriodicSegment_eq_source] using C.gap
  other := by simpa only [physicalPeriodicSegment_eq_source] using C.other

/-- Every real physical source admits an isolating circle at every index, including collapsed gaps. -/
theorem exists_physicalSpectralCircle (u : physicalRealSubmodule) (n : ℤ) :
    Nonempty (PhysicalSpectralCircle u.val n) := by
  let φ := sourcePhysicalL2Equiv.symm u.val
  obtain ⟨N,ε,_,_,V,_,_,hφV,c,hD⟩ :=
    exists_local_source_quantitative_isolating_discs (by simp) (by norm_num) φ u.property
  obtain ⟨a,r,hr,he⟩ := hD.discs n
  exact ⟨PhysicalSpectralCircle.ofSource (hD.periodCircle φ hφV n a r hr he)⟩

/-- The intrinsic canonical root is nonzero everywhere on an isolating circle. -/
theorem PhysicalSpectralCircle.root_ne_zero {u : IntervalPairL2} {n : ℤ}
    (C : PhysicalSpectralCircle u n) (z : ℂ) (hz : z ∈ sphere (C.center:ℂ) C.radius) :
    physicalCanonicalProductRoot u z ≠ 0 := by
  apply physicalCanonicalProductRoot_ne_zero
  rw [physicalSpectralRootDomain_eq_source]
  exact C.toSource.sphere_subset_rootDomain hz

/-- Every physical isolating circle computes the actual indexed action. -/
theorem PhysicalSpectralCircle.action {u : IntervalPairL2} {n : ℤ}
    (C : PhysicalSpectralCircle u n) :
    physicalIndexedAction n u = (Real.pi:ℂ)⁻¹ *
      ∮ z in C((C.center:ℂ),C.radius), z*deriv (l2Discriminant u) z/physicalCanonicalProductRoot u z := by
  simpa only [physicalCanonicalProductRoot_eq,PhysicalSpectralCircle.toSource] using
    physicalIndexedAction_eq_circle u n C.toSource

end NLS.ZakharovShabat
