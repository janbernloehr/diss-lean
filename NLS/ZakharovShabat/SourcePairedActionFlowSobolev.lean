import NLS.ZakharovShabat.SourcePairedActionFlowDiagonal
import NLS.ZakharovShabat.SourceBirkhoffSobolevRegularity

/-! # The complete action flow preserves every native Sobolev order

Original periodic spectral data include their canonically labelled gap
sequence. The existing source/gap regularity theorem therefore transfers
every nonnegative real Sobolev order along the full isospectral flow.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem sourcePeriodicGapDisplacement_eq_of_isospectral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ) :
    sourcePeriodicGapDisplacement hp hp1 ψ.val = sourcePeriodicGapDisplacement hp hp1 φ.val := by
  obtain ⟨hl,hr⟩ := canonicalPeriodicEndpoints_eq_of_spectral_data hp hp1
    (periodOnePotential ψ.val) (periodOnePotential φ.val)
    (periodOnePotential_mem _) (periodOnePotential_mem _) h.1 h.2
  ext n
  simp only [sourcePeriodicGapDisplacement_apply,canonicalPeriodicGap,hl,hr]

theorem source_sobolev_mem_iff_of_isospectral (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (h : ψ ∈ sourceIsospectralSet hp φ)
    (σ : ℝ) (hσ : 0 ≤ σ) :
    (Memℓp (fun j : ℤ => (Weight.sobolev σ j : ℂ)*ψ.val.fst j) p ∧
      Memℓp (fun j : ℤ => (Weight.sobolev σ j : ℂ)*ψ.val.snd j) p) ↔
    (Memℓp (fun j : ℤ => (Weight.sobolev σ j : ℂ)*φ.val.fst j) p ∧
      Memℓp (fun j : ℤ => (Weight.sobolev σ j : ℂ)*φ.val.snd j) p) := by
  rw [source_sobolev_mem_iff_gap_mem hp hp1 ψ σ hσ,
    source_sobolev_mem_iff_gap_mem hp hp1 φ σ hσ,
    sourcePeriodicGapDisplacement_eq_of_isospectral hp hp1 φ ψ h]

namespace SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

theorem hilbertPairedActionFlow_mem_isospectralSet
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k l : ℤ) (t : ℝ) :
    D.hilbertPairedActionFlow φ k l t ∈ sourceIsospectralSet (by simp) φ :=
  (mem_sourceIsospectralSet_iff_discriminant_eq (by simp) (by norm_num) φ _).mpr
    (D.discriminant_hilbertPairedActionFlow φ k l t)

/-- The full original Sobolev regularity is preserved and reflected at
every time. In particular every original real H1 diagonal stays H1. -/
theorem hilbertPairedActionFlow_sobolev_mem_iff
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k l : ℤ) (t σ : ℝ) (hσ : 0 ≤ σ) :
    (Memℓp (fun j : ℤ => (Weight.sobolev σ j : ℂ)*
      (D.hilbertPairedActionFlow φ k l t).val.fst j) 2 ∧
      Memℓp (fun j : ℤ => (Weight.sobolev σ j : ℂ)*
        (D.hilbertPairedActionFlow φ k l t).val.snd j) 2) ↔
    (Memℓp (fun j : ℤ => (Weight.sobolev σ j : ℂ)*φ.val.fst j) 2 ∧
      Memℓp (fun j : ℤ => (Weight.sobolev σ j : ℂ)*φ.val.snd j) 2) :=
  source_sobolev_mem_iff_of_isospectral (by simp) (by norm_num) φ _
    (D.hilbertPairedActionFlow_mem_isospectralSet φ k l t) σ hσ

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
