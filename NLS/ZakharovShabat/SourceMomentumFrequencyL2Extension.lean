import NLS.ZakharovShabat.SourceMomentumFrequencyNormalization
import NLS.ZakharovShabat.SourceSobolevOpenGapDensity
import NLS.ZakharovShabat.SourceSobolevPhysicalCorrection

/-! # Unique continuous extension of the original NLS momentum frequency to L²

Real H¹ open-gap density removes the selected-angle restriction there.
The actual L² finite-gap density and unchanged H¹ reconstruction then
give uniqueness on the entire original real L² source, including closed gaps.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

def sourceRealH1Inclusion (a : realTypeSobolevSourceLocus) : realTypeSourceSubmodule 2 :=
  ⟨sobolevSourceInclusion a.val,a.property⟩

theorem continuous_sourceRealH1Inclusion : Continuous sourceRealH1Inclusion :=
  (sobolevSourceInclusion.continuous.comp continuous_subtype_val).subtype_mk _

def IsSourceMomentumFrequencyExtension (A : SourceMomentumFrequencyFamily) (n : ℤ)
    (f : realTypeSourceSubmodule 2 → ℂ) : Prop :=
  Continuous f ∧ ∀ a : realTypeSobolevSourceLocus,
    canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (sobolevSourceInclusion a.val))
      (periodOnePotential_mem _) n ≠ 0 → f (sourceRealH1Inclusion a) = sourceSobolevThetaMomentumBracket n A.psi a.val

theorem sourceMomentumFrequency_extension (A : SourceMomentumFrequencyFamily) (n : ℤ) :
    IsSourceMomentumFrequencyExtension A n (fun φ => sourceMomentumFrequency n φ.val) :=
  ⟨continuous_const,fun a ha => A.frequency_eq_original_bracket a n ha⟩

theorem sourceMomentumFrequency_extension_H1_unique (A : SourceMomentumFrequencyFamily) (n : ℤ)
    (f : realTypeSourceSubmodule 2 → ℂ) (hf : IsSourceMomentumFrequencyExtension A n f)
    (a : realTypeSobolevSourceLocus) : f (sourceRealH1Inclusion a) = 2*(Real.pi : ℂ)*n := by
  have hc : IsClosed {b : realTypeSobolevSourceLocus | f (sourceRealH1Inclusion b) = 2*(Real.pi : ℂ)*n} :=
    isClosed_eq (hf.1.comp continuous_sourceRealH1Inclusion) continuous_const
  have hs : sourceSobolevOpenGapRealLocus n ⊆
      {b : realTypeSobolevSourceLocus | f (sourceRealH1Inclusion b) = 2*(Real.pi : ℂ)*n} := by
    intro b hb
    exact (hf.2 b hb).trans (A.normalization b n hb)
  exact closure_minimal hs hc (dense_sourceSobolevOpenGapRealLocus n a)

/-- Every continuous extension agreeing with the actual original
angle-S_2 bracket is the same constant on ALL real L² profiles. -/
theorem sourceMomentumFrequency_extension_unique (A : SourceMomentumFrequencyFamily) (n : ℤ)
    (f : realTypeSourceSubmodule 2 → ℂ) (hf : IsSourceMomentumFrequencyExtension A n f) :
    f = (fun φ => sourceMomentumFrequency n φ.val) := by
  funext φ
  have hc : IsClosed {ψ : realTypeSourceSubmodule 2 | f ψ = 2*(Real.pi : ℂ)*n} :=
    isClosed_eq hf.1 continuous_const
  have hs : sourceFiniteGapLocus (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num) ⊆
      {ψ : realTypeSourceSubmodule 2 | f ψ = 2*(Real.pi : ℂ)*n} := by
    intro ψ hψ
    let χ : realTypeSourceSubmodule 2 := ⟨ψ.val,ψ.property⟩
    have hχ : χ ∈ sourceFiniteGapLocus (by simp) (by norm_num) := hψ
    let b := sourceFiniteGapSobolevPair (by simp) (by norm_num) χ hχ
    have hinc : sobolevSourceInclusion b = χ.val := sobolevSourceInclusion_sourceFiniteGapSobolevPair χ hχ
    have hb : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion b)) := by
      rw [hinc]
      exact χ.property
    have he : sourceRealH1Inclusion ⟨b,hb⟩ = χ := by
      apply Subtype.ext
      exact hinc
    change f χ = 2*(Real.pi : ℂ)*n
    rw [← he]
    exact sourceMomentumFrequency_extension_H1_unique A n f hf ⟨b,hb⟩

  exact closure_minimal hs hc (dense_sourceFiniteGapLocus (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num) φ)

theorem existsUnique_sourceMomentumFrequencyExtension (A : SourceMomentumFrequencyFamily) (n : ℤ) :
    ∃! f : realTypeSourceSubmodule 2 → ℂ, IsSourceMomentumFrequencyExtension A n f := by
  refine ⟨_,sourceMomentumFrequency_extension A n,?_⟩
  intro f hf
  exact sourceMomentumFrequency_extension_unique A n f hf

end NLS.ZakharovShabat
