import NLS.Fourier.PeriodOneSmoothSynthesis
import NLS.ZakharovShabat.SourceFiniteGapMassExponent
import NLS.ZakharovShabat.NLSWKBComparison

/-! # Smooth physical representatives of the original finite-gap source

The absolutely convergent period-one Fourier series preserve every source
coefficient and are smooth by the all-order Sobolev bootstrap. Their actual
classical discriminant equals the canonical discriminant at every finite
source exponent greater than one.
-/
noncomputable section
open Set Complex NLS.Fourier
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original source coefficients, realized by their actual period-one
Fourier sums; finite Fourier support is not required. -/
def sourceFiniteGapPhysicalPair (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    (ℝ → ℂ) × (ℝ → ℂ) :=
  (periodOneSynthesis ⟨_,(sourceFiniteGap_memlp_one hp hp1 φ hf).1⟩,
   periodOneSynthesis ⟨_,(sourceFiniteGap_memlp_one hp hp1 φ hf).2⟩)

theorem contDiff_sourceFiniteGapPhysicalPair (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ContDiff ℝ ∞ (sourceFiniteGapPhysicalPair hp hp1 φ hf).1 ∧
      ContDiff ℝ ∞ (sourceFiniteGapPhysicalPair hp hp1 φ hf).2 := by
  exact ⟨contDiff_periodOneSynthesis_of_all_sobolev hp _
    (fun s hs => (sourceFiniteGap_mem_all_sobolev hp hp1 φ hf s hs).1),
    contDiff_periodOneSynthesis_of_all_sobolev hp _
    (fun s hs => (sourceFiniteGap_mem_all_sobolev hp hp1 φ hf s hs).2)⟩

theorem periodic_sourceFiniteGapPhysicalPair (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    Function.Periodic (sourceFiniteGapPhysicalPair hp hp1 φ hf).1 1 ∧
      Function.Periodic (sourceFiniteGapPhysicalPair hp hp1 φ hf).2 1 :=
  ⟨periodOneSynthesis_periodic _,periodOneSynthesis_periodic _⟩

/-- Fourier integrals of the smooth representative recover the original
coefficients, with the original signs and period-one normalization. -/
theorem periodOneCoefficient_sourceFiniteGapPhysicalPair (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (n : ℤ) :
    periodOneCoefficient (sourceFiniteGapPhysicalPair hp hp1 φ hf).1 n = φ.val.fst n ∧
      periodOneCoefficient (sourceFiniteGapPhysicalPair hp hp1 φ hf).2 n = φ.val.snd n :=
  ⟨periodOneCoefficient_synthesis _ n,periodOneCoefficient_synthesis _ n⟩

/-- The canonical trace is exactly the trace of this smooth classical
representative. The original Banach exponent is unrestricted below infinity. -/
theorem sourceFiniteGap_discriminant_eq_smooth (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) (z : ℂ) :
    canonicalDiscriminant hp (periodOnePotential φ.val) z =
      classicalDiscriminant (classicalPotentialOfFunctions
        (sourceFiniteGapPhysicalPair hp hp1 φ hf).1 (sourceFiniteGapPhysicalPair hp hp1 φ hf).2
        (contDiff_sourceFiniteGapPhysicalPair hp hp1 φ hf).1.continuous
        (contDiff_sourceFiniteGapPhysicalPair hp hp1 φ hf).2.continuous) z := by
  obtain ⟨ψ,hcoeff,_,_⟩ := sourceFiniteGap_exists_hilbert_mass_model hp hp1 φ hf
  have hΔ : canonicalDiscriminant hp (periodOnePotential φ.val) z =
      canonicalDiscriminant (by simp) (periodOnePotential ψ.val) z := by
    rcases le_total p 2 with hp2 | h2p
    · have he : CoeffPair.exponentInclusion hp2 φ.val = ψ.val := by
        apply (CoeffPair.toMax 2).injective
        apply Prod.ext
        · ext n
          exact (hcoeff n).1.symm
        · ext n
          exact (hcoeff n).2.symm
      rw [sourceDiscriminant_exponent hp (by simp) hp2 φ.val z,he]
    · have he : CoeffPair.exponentInclusion h2p ψ.val = φ.val := by
        apply (CoeffPair.toMax p).injective
        apply Prod.ext
        · ext n
          exact (hcoeff n).1
        · ext n
          exact (hcoeff n).2
      simpa only [he] using (sourceDiscriminant_exponent (by simp) hp h2p ψ.val z).symm
  let a : Coeff 1 := ⟨_,(sourceFiniteGap_memlp_one hp hp1 φ hf).1⟩
  let b : Coeff 1 := ⟨_,(sourceFiniteGap_memlp_one hp hp1 φ hf).2⟩
  have hphysical := physicalBase_absoluteSourceCurve ψ.val a b
    (fun n => (hcoeff n).1.symm) (fun n => (hcoeff n).2.symm)
  exact hΔ.trans (canonicalDiscriminant_eq_classical _ (periodOnePotential_mem _) _ hphysical z)

end NLS.ZakharovShabat
