import NLS.ZakharovShabat.PhysicalPsiComparison
import NLS.ZakharovShabat.SourcePhysicalBirkhoffComplex

/-! # Physical normalized functions in the original Birkhoff family

The independently specified physical gap roots agree with every original
Section 14 family. They depend real analytically on the physical Hilbert
source and extend complex analytically to that family's physical domain.
-/

noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The independently selected physical roots vary real analytically in the native Hilbert norm. -/
theorem analyticOnNhd_physicalPsiGapRoot (n : ℤ) :
    AnalyticOnNhd ℝ (physicalPsiGapRoot n) univ := by
  intro u _
  have h := (analyticAt_sourcePsiGapRoot_real (by simp) (by norm_num) n
    (realSourcePhysicalL2Equiv.symm u)).comp
      (realSourcePhysicalL2Equiv.symm.toContinuousLinearEquiv.analyticAt u)
  convert h using 1
  funext v
  exact physicalPsiGapRoot_eq_source n v

/-- The zero potential has the undeformed deleted lattice roots, including the collapsed gaps. -/
@[simp] theorem physicalPsiGapRoot_zero (n : ℤ) : physicalPsiGapRoot n 0 = 0 := by
  rw [physicalPsiGapRoot_eq_source]
  simpa only [ZeroMemClass.coe_zero, map_zero] using
    sourcePsiGapRoot_zero (p := 2) (by simp) (by norm_num) n

/-- The physical complex extension of a specified normalized root family. -/
def physicalPsiRootExtension (s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n)
    (n : ℤ) (u : IntervalPairL2) : DeletedCoeff 2 n := s n (sourcePhysicalL2Equiv.symm u)

namespace SourceSection14OriginalData
variable {W₀ W V : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
  (D : SourceSection14OriginalData (by simp) (by norm_num) W₀ W V s)

include D

/-- Every original family has exactly the independently specified physical roots on the real form. -/
theorem physicalPsiGapRoot_eq_family (n : ℤ) (u : physicalRealSubmodule) :
    physicalPsiGapRoot n u = physicalPsiRootExtension s n u.val := by
  rw [physicalPsiGapRoot_eq_source]
  exact (D.previous.previous.previous.psi.real_agreement n
    ⟨sourcePhysicalL2Equiv.symm u.val,u.property⟩).symm

/-- The literal physical entire numerator equals the one used in the original Birkhoff map. -/
theorem physicalPsiFunction_eq_family (n : ℤ) (u : physicalRealSubmodule) (z : ℂ) :
    physicalPsiFunction n u z =
      sourcePsiCandidate n (z,(s n (sourcePhysicalL2Equiv.symm u.val) : Coeff 2)) := by
  rw [physicalPsiFunction,D.physicalPsiGapRoot_eq_family]
  rfl

/-- The normalized root family extends holomorphically to the original physical Birkhoff domain. -/
theorem physicalPsiRootExtension_analytic (n : ℤ) :
    AnalyticOnNhd ℂ (physicalPsiRootExtension s n) (physicalBirkhoffDomain V) := by
  intro u hu
  exact (D.previous.previous.previous.psi.analytic n _ (D.complex.source_subset hu)).comp
    (sourcePhysicalL2Equiv.symm.toContinuousLinearEquiv.analyticAt u)

/-- Exact physical period normalization persists for complex inputs and every supplied isolating circle. -/
theorem physicalPsiRootExtension_period (n m : ℤ) (u : IntervalPairL2)
    (hu : u ∈ physicalBirkhoffDomain V) (C : PhysicalSpectralCircle u m) :
    (2*Real.pi:ℂ)⁻¹*(∮ z in C((C.center:ℂ),C.radius),
      (-2*jointDeletedSingleSpectralProduct n (z,(physicalPsiRootExtension s n u : Coeff 2)))/
        physicalCanonicalProductRoot u z) = if m = n then 1 else 0 := by
  have h := D.previous.previous.previous.psi.period (sourcePhysicalL2Equiv.symm u)
    (D.complex.source_subset hu) n m C.toSource
  simpa only [sourcePsiContour, sourcePsiContourIntegrandJoint, sourcePsiCandidate,
    physicalPsiRootExtension, physicalCanonicalProductRoot_eq, physicalCanonicalRoot,
    PhysicalSpectralCircle.toSource] using h

end SourceSection14OriginalData
end NLS.ZakharovShabat
