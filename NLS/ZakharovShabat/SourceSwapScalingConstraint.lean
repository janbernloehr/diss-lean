import NLS.ZakharovShabat.SourceReflectionCutDomain
import NLS.ZakharovShabat.L2DiscriminantPointwiseSymmetries

/-! # Spectral parity at a source fixed by swap up to reciprocal scaling -/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

theorem sourcePeriodicReflection_of_swap_scaling (c : ℂ) (hc : c ≠ 0) (φ : CoeffPair 2)
    (hP : sourceComponentSwap φ = sourceReciprocalScaling c φ) :
    SourcePeriodicReflection (by simp) (by norm_num) φ := by
  obtain ⟨hl,hr⟩ := sourceCanonicalPeriodicEndpoints_reciprocalScaling
    (by simp) (by norm_num) c hc φ
  intro n
  have h := sourceCanonicalPeriodicEndpoints_componentSwap (by simp) (by norm_num) φ (-n)
  simpa only [neg_neg,hP,hl,hr] using h

theorem source_swap_scaling_xi_odd (c : ℂ) (hc : c ≠ 0) (φ : CoeffPair 2)
    (hP : sourceComponentSwap φ = sourceReciprocalScaling c φ) (z : ℂ) (x : ℝ) :
    l2WholeLineDiscriminantXi (sourcePhysicalL2 φ) (-z) x =
      -l2WholeLineDiscriminantXi (sourcePhysicalL2 φ) z x := by
  have h := l2WholeLineDiscriminantXi_sourceComponentSwap φ z x
  simpa only [hP,l2WholeLineDiscriminantXi_sourceReciprocalScaling c hc] using h

theorem source_swap_scaling_normalized_xi_even (c : ℂ) (hc : c ≠ 0) (φ : CoeffPair 2)
    (hP : sourceComponentSwap φ = sourceReciprocalScaling c φ) (z : ℂ) (x : ℝ) :
    l2WholeLineDiscriminantXi (sourcePhysicalL2 φ) (-z) x/sourceCanonicalRoot (by simp) (by norm_num) φ (-z) =
      l2WholeLineDiscriminantXi (sourcePhysicalL2 φ) z x/sourceCanonicalRoot (by simp) (by norm_num) φ z := by
  rw [source_swap_scaling_xi_odd c hc φ hP,
    (sourcePeriodicReflection_of_swap_scaling c hc φ hP).canonicalRoot_neg]
  exact neg_div_neg_eq _ _

end NLS.ZakharovShabat
