import NLS.Articles.KdVKdV2Frequencies.FiniteGapRoughFirstVariation

/-! # Actual intrinsic hierarchy frequencies are analytic on native real sources -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.ZakharovShabat
namespace NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData

/-- The intrinsic physical frequency has a real analytic source dependence
on the ENTIRE original native real mean-zero space, including closed modes. -/
theorem nativeSourceHierarchyFrequency_analytic (D : GlobalRoughAbelianForwardData)
    (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2)) (n : ℕ+) :
    AnalyticOnNhd ℝ (fun q => D.nativeSourceHierarchyFrequency m r hrs q n) univ := by
  obtain ⟨U,ω,_hU,hsub,hω,he⟩ := D.exists_originalHierarchyFrequency_native_analytic_extensions m r hrs
  have heq : (fun q => D.nativeSourceHierarchyFrequency m r hrs q n) =
      fun q => ω n (D.nativeSourceActionSequence m r hrs q) := by
    funext q
    exact (he (originalPositiveActions m r hrs (D.rawIntegerForwardHomeomorph m q)) n).symm
  rw [heq]
  intro q _
  have hωq : AnalyticAt ℝ (ω n) (D.nativeSourceActionSequence m r hrs q) :=
    hω n _ (hsub (originalPositiveActions m r hrs (D.rawIntegerForwardHomeomorph m q)).property)
  exact hωq.comp (f := D.nativeSourceActionSequence m r hrs)
    (D.nativeSourceActionSequence_analytic m r hrs q (mem_univ _))

/-- Actual frequency continuity retains both the native source norm and
the original physical action derivative at all zero and nonzero actions. -/
theorem continuous_nativeSourceHierarchyFrequency (D : GlobalRoughAbelianForwardData)
    (m : ℕ) (r : ℝ) (hrs : r=2*((m : ℝ)+1/2)) (n : ℕ+) :
    Continuous (fun q => D.nativeSourceHierarchyFrequency m r hrs q n) :=
  continuous_iff_continuousAt.mpr (fun q => (D.nativeSourceHierarchyFrequency_analytic m r hrs n q (mem_univ _)).continuousAt)

end NLS.Articles.KdVKdV2Frequencies.GlobalRoughAbelianForwardData
