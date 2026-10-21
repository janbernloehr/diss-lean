import NLS.ZakharovShabat.PeriodOneSobolevMomentum
import NLS.ZakharovShabat.SourceSobolevFiniteGapDensity
import NLS.ZakharovShabat.SourceFiniteGapAngleSobolev

noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ComplexConjugate
namespace NLS.ZakharovShabat

/-- Actual real finite-gap sources with nonzero physical momentum exist.
The witness is obtained by H¹ finite-gap density near a signed Fourier mode. -/
theorem exists_sourceFiniteGap_nonzero_momentum :
    ∃ φ : realTypeSourceSubmodule 2, ∃ hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num),
      sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 2 ≠ 0 := by
  let a : realTypeSobolevSourceLocus := ⟨(scalarMode (-1) 1,scalarMode 1 1),by
    intro n
    change (sobolevSourceInclusion (scalarMode (-1) 1,scalarMode 1 1)).snd n =
      conj ((sobolevSourceInclusion (scalarMode (-1) 1,scalarMode 1 1)).fst (-n))
    simp only [sobolevSourceInclusion_snd,sobolevSourceInclusion_fst,scalarMode_apply]
    have he : (-n = -1) ↔ n = 1 := by omega
    simp [he]⟩
  have ha : periodOneSobolevMomentum a.val ≠ 0 := by
    have he : periodOneSobolevMomentum a.val = 2*(Real.pi:ℂ) := by
      simpa only [Int.cast_one,mul_one] using periodOneSobolevMomentum_scalarModes 1 1 1
    rw [he]
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  let V : Set realTypeSobolevSourceLocus := {b | periodOneSobolevMomentum b.val ≠ 0}
  have hV : IsOpen V :=
    (continuous_periodOneSobolevMomentum.comp continuous_subtype_val).isOpen_preimage _ isOpen_ne
  obtain ⟨b,hb,hbm,_⟩ := exists_sourceSobolevFiniteGap_mem_open V hV a ha 1 (by norm_num)
  let φ : realTypeSourceSubmodule 2 := ⟨sobolevSourceInclusion b.val,b.property⟩
  have hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num) := hb
  have he : sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf = b.val :=
    sobolevSourceInclusion_injective (sobolevSourceInclusion_sourceFiniteGapSobolevPair φ hf)
  refine ⟨φ,hf,?_⟩
  rw [← periodOneSobolevMomentum_sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf,he]
  exact hbm

end NLS.ZakharovShabat
