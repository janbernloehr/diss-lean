import NLS.ZakharovShabat.PhysicalEnergyCotangent
import NLS.ZakharovShabat.SourcePhysicalEnergyActionDifferential
import NLS.ZakharovShabat.SourceFiniteGapNLSVariation

/-! # The classical NLS field in the original Hilbert source space

The Fourier coefficients of the smooth physical finite-gap NLS field form
an actual Hilbert source. Every Hilbert cotangent restricting to the physical
H¹ energy derivative generates exactly this field under the original Poisson
structure. The total sequence constructor is proved to recover all coefficients.
-/
noncomputable section
open Set Complex NLS.Fourier NLS.Poisson
namespace NLS.ZakharovShabat

/-- The classical physical NLS field, represented in the original coefficient space. -/
def sourceFiniteGapPhysicalNLSCoefficients (φ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) : CoeffPair 2 :=
  (CoeffPair.toMax 2).symm
    (Coeff.ofFunctionOrZero 2 (periodOneCoefficient (sourceFiniteGapPhysicalNLSVectorField (by simp) (by norm_num) φ hf).1),
     Coeff.ofFunctionOrZero 2 (periodOneCoefficient (sourceFiniteGapPhysicalNLSVectorField (by simp) (by norm_num) φ hf).2))

/-- Any physical energy cotangent has the exact classical NLS direction in source norm. -/
theorem sourceFiniteGapPhysicalNLSCoefficients_eq_HamiltonianDirection
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (L : CoeffPair 2 →L[ℂ] ℂ)
    (hL : HasFDerivAt periodOneSobolevHamiltonian (L.comp sobolevSourceInclusion)
      (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf)) :
    sourceFiniteGapPhysicalNLSCoefficients φ hf = sourceHamiltonianDirection le_rfl L := by
  let a := sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf
  obtain ⟨ha,hb⟩ := periodOneSobolevSynthesis_sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf
  obtain ⟨hsa,hsb⟩ := contDiff_sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf
  have hc (n : ℤ) := sourceHamiltonianDirection_physicalEnergy_coordinates a.1 a.2
    (by rw [ha]; exact hsa) (by rw [hb]; exact hsb) L hL n
  have he (n : ℤ) :
      (sourceHamiltonianDirection le_rfl L).fst n =
        periodOneCoefficient (sourceFiniteGapPhysicalNLSVectorField (by simp) (by norm_num) φ hf).1 n ∧
      (sourceHamiltonianDirection le_rfl L).snd n =
        periodOneCoefficient (sourceFiniteGapPhysicalNLSVectorField (by simp) (by norm_num) φ hf).2 n := by
    simpa only [a,ha,hb,sourceFiniteGapPhysicalNLSVectorField] using! hc n
  apply (CoeffPair.toMax 2).injective
  change (Coeff.ofFunctionOrZero 2 _,Coeff.ofFunctionOrZero 2 _) =
    ((sourceHamiltonianDirection le_rfl L).fst,(sourceHamiltonianDirection le_rfl L).snd)
  exact Prod.ext (Coeff.ofFunctionOrZero_eq_of_coordinates _ _ (fun n => (he n).1))
    (Coeff.ofFunctionOrZero_eq_of_coordinates _ _ (fun n => (he n).2))

/-- The physical energy at any finite-gap source has a bounded Hilbert cotangent. -/
theorem exists_sourceFiniteGapPhysicalEnergy_cotangent
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ L : CoeffPair 2 →L[ℂ] ℂ,
      HasFDerivAt periodOneSobolevHamiltonian (L.comp sobolevSourceInclusion)
        (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf) := by
  obtain ⟨W,P,_,_,_,_,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas (p := 2) (by simp) (by norm_num)
  let a := sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf
  have ha : sobolevSourceInclusion a = φ.val := sobolevSourceInclusion_sourceFiniteGapSobolevPair φ hf
  have hr : IsRealType (CoeffPair.toMax 2 (sobolevSourceInclusion a)) := ha ▸ φ.property
  have hsub : (⟨sobolevSourceInclusion a,hr⟩ : realTypeSourceSubmodule 2) = φ := Subtype.ext ha
  have hfa : (⟨a,hr⟩ : realTypeSobolevSourceLocus) ∈ sourceSobolevFiniteGapLocus := by
    change (⟨sobolevSourceInclusion a,hr⟩ : realTypeSourceSubmodule 2) ∈ sourceFiniteGapLocus (by simp) (by norm_num)
    rwa [hsub]
  obtain ⟨S,hS⟩ := A.exists_periodOneSobolevHamiltonian_finiteGap_differential
    hs.toSourcePsiIsolatingComplexExtension ⟨a,hr⟩ hfa
  exact ⟨_,hS ▸ (analyticAt_periodOneSobolevHamiltonian a).differentiableAt.hasFDerivAt⟩

/-- Both coordinates of the constructed source are the actual physical Fourier integrals. -/
theorem sourceFiniteGapPhysicalNLSCoefficients_apply
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) :
    (sourceFiniteGapPhysicalNLSCoefficients φ hf).fst n =
      periodOneCoefficient (sourceFiniteGapPhysicalNLSVectorField (by simp) (by norm_num) φ hf).1 n ∧
    (sourceFiniteGapPhysicalNLSCoefficients φ hf).snd n =
      periodOneCoefficient (sourceFiniteGapPhysicalNLSVectorField (by simp) (by norm_num) φ hf).2 n := by
  obtain ⟨L,hL⟩ := exists_sourceFiniteGapPhysicalEnergy_cotangent φ hf
  rw [sourceFiniteGapPhysicalNLSCoefficients_eq_HamiltonianDirection φ hf L hL]
  let a := sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf
  obtain ⟨ha,hb⟩ := periodOneSobolevSynthesis_sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf
  obtain ⟨hsa,hsb⟩ := contDiff_sourceFiniteGapPhysicalPair (by simp) (by norm_num) φ hf
  have hc := sourceHamiltonianDirection_physicalEnergy_coordinates a.1 a.2
    (by rw [ha]; exact hsa) (by rw [hb]; exact hsb) L hL n
  simpa only [a,ha,hb,sourceFiniteGapPhysicalNLSVectorField] using! hc

/-- The physical NLS source field is tangent to the original real source form. -/
theorem sourceFiniteGapPhysicalNLSCoefficients_real
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    IsRealType (CoeffPair.toMax 2 (sourceFiniteGapPhysicalNLSCoefficients φ hf)) := by
  intro n
  change (sourceFiniteGapPhysicalNLSCoefficients φ hf).snd n =
    starRingEnd ℂ ((sourceFiniteGapPhysicalNLSCoefficients φ hf).fst (-n))
  rw [(sourceFiniteGapPhysicalNLSCoefficients_apply φ hf n).2,
    (sourceFiniteGapPhysicalNLSCoefficients_apply φ hf (-n)).1]
  have he : (sourceFiniteGapPhysicalNLSVectorField (by simp) (by norm_num) φ hf).2 =
      fun x => starRingEnd ℂ ((sourceFiniteGapPhysicalNLSVectorField (by simp) (by norm_num) φ hf).1 x) :=
    funext (sourceFiniteGapPhysicalNLSVectorField_real (by simp) (by norm_num) φ hf)
  simp only [periodOneCoefficient,← unitFourierCoefficient_eq_fourierCoeffOn,he,unitFourierCoefficient_conj]

end NLS.ZakharovShabat
