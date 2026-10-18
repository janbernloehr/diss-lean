import NLS.ZakharovShabat.SourcePhysicalBirkhoffComplex

/-! # Constructed physical Hilbert Birkhoff map

An original Section 14 family constructs the physical Hilbert map, its
global analytic inverse, norm preservation, and complex extension together.
Identification with a separately formalized external book construction
still requires matching its spectral and angle primitives.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Construct the physical Hilbert map and both analytic directions from the original family. -/
theorem sourceSection14_physicalHilbert :
    ∃ W₀ W V : Set (CoeffPair 2), ∃ s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n,
      ∃ _D : SourceSection14Data (by simp) (by norm_num) W₀ W V s,
      ∃ e : physicalRealSubmodule ≃ₜ PhysicalRealBirkhoffTarget,
        AnalyticOnNhd ℝ e univ ∧ AnalyticOnNhd ℝ e.symm univ ∧
        (∀ u, ‖e u‖ = ‖u‖) ∧
        IsOpen (physicalBirkhoffDomain V) ∧
        (∀ u : physicalRealSubmodule, u.val ∈ physicalBirkhoffDomain V) ∧
        AnalyticOnNhd ℂ (physicalBirkhoffMap s) (physicalBirkhoffDomain V) ∧
        (∀ u, physicalRealTargetComplex (e u) = physicalBirkhoffMap s u.val) ∧
        ∀ (u : physicalRealSubmodule) (n : ℤ),
          (e u).fst n = Real.sqrt (2*(physicalIndexedAction n u.val).re)*
            Real.cos (sourceAngularOriginalTheta (by simp) (by norm_num) n s
              (sourcePhysicalL2Equiv.symm u.val)).re ∧
          (e u).snd n = Real.sqrt (2*(physicalIndexedAction n u.val).re)*
            Real.sin (sourceAngularOriginalTheta (by simp) (by norm_num) n s
              (sourcePhysicalL2Equiv.symm u.val)).re := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection14 (p := 2) (by simp) (by norm_num)
  let A := D.toSourceSection14OriginalData
  exact ⟨W₀,W,V,s,D,A.physicalRealActionAngleHomeomorph,
    A.physicalRealActionAngleHomeomorph_analytic.1,A.physicalRealActionAngleHomeomorph_analytic.2,
    A.physicalRealActionAngleHomeomorph_norm,A.physicalBirkhoffDomain_open,A.physicalBirkhoffDomain_real,
    A.physicalBirkhoffMap_analytic,A.physicalBirkhoffMap_real,A.physicalRealActionAngleHomeomorph_formula⟩

end NLS.ZakharovShabat
