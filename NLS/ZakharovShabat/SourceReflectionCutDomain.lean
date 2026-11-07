import NLS.ZakharovShabat.SourceReflectionBoundaryConstant
import NLS.ZakharovShabat.SourceCanonicalRootReflection

/-! # The full spectral cut domain at pure-T-even and pure-T-odd sources -/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

theorem sourcePeriodicReflection_of_midpoint_even_or_odd (φ : CoeffPair 2)
    (hT : sourceMidpointReflection φ = φ ∨ sourceMidpointReflection φ = -φ) :
    SourcePeriodicReflection (by simp) (by norm_num) φ := by
  obtain ⟨hl,hr⟩ := sourceCanonicalPeriodicEndpoints_reciprocalScaling
    (by simp) (by norm_num) (-1) (by norm_num) φ
  rw [sourceReciprocalScaling_neg_one] at hl hr
  intro n
  have h := sourceCanonicalPeriodicEndpoints_midpointReflection (by simp) (by norm_num) φ (-n)
  simp only [neg_neg] at h
  rcases hT with hT | hT
  · simpa only [hT] using h
  · simpa only [hT,hl,hr] using h

theorem source_midpoint_even_or_odd_neg_mem_rootDomain_iff (φ : CoeffPair 2)
    (hT : sourceMidpointReflection φ = φ ∨ sourceMidpointReflection φ = -φ) (z : ℂ) :
    -z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) φ ↔
      z ∈ sourceCanonicalRootDomain (by simp) (by norm_num) φ :=
  (sourcePeriodicReflection_of_midpoint_even_or_odd φ hT).neg_mem_rootDomain_iff z

end NLS.ZakharovShabat
