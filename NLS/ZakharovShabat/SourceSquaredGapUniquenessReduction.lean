import NLS.ZakharovShabat.SymmetricSourceCoordinates

/-! # Reduction of Hilbert squared-gap spectral uniqueness to signed-gap injectivity

Every actual Hilbert isospectral set has a symmetric representative whose
signed gaps are nonpositive. Equal squared gaps therefore give equal signed
gaps for these representatives. Global injectivity of the actual symmetric
signed-gap map would then imply equality of the original periodic spectra,
with algebraic multiplicities. The injectivity premise remains explicit.
-/
noncomputable section
open Set Complex
namespace NLS.ZakharovShabat

/-- Every actual Hilbert spectrum has symmetric Fourier coordinates with nonpositive signed gaps. -/
theorem exists_symmetric_coordinates_isospectral_nonpos_signed_gaps
    (φ : realTypeSourceSubmodule 2) :
    ∃ a : RealCoeff 2,
      symmetricRealSourceCoefficients 2 a ∈ sourceIsospectralSet (by simp) φ ∧
      ∀ n, symmetricSourceSignedGapMap (by simp) (by norm_num) a n ≤ 0 := by
  let μ n := (canonicalPeriodicLeft (by simp) (by norm_num)
    (periodOnePotential φ.val) (periodOnePotential_mem _) n).re
  obtain ⟨χ,hχ,_⟩ := existsUnique_symmetric_source_with_endpoint_dirichletData φ μ (fun _ => Or.inl rfl)
  let a := Coeff.reCLM 2 χ.val.val.snd
  have ha : symmetricRealSourceCoefficients 2 a = χ.val :=
    symmetricRealSourceCoefficients_reconstruct χ.val hχ.1
  have hc : symmetricSourceCoefficients 2 a = χ.val.val := congrArg Subtype.val ha
  refine ⟨a,ha.symm ▸ χ.property,fun n => ?_⟩
  have he := canonicalPeriodicEndpoints_eq_of_spectral_data (by simp) (by norm_num)
    (periodOnePotential χ.val.val) (periodOnePotential φ.val)
    (periodOnePotential_mem _) (periodOnePotential_mem _) χ.property.1 χ.property.2
  have hν := canonicalPeriodOneBoundaryRoots_mem_gap (by simp) (by norm_num) .neumann χ.val.val χ.val.property n
  rw [he.1,he.2] at hν
  rw [symmetricSourceSignedGapMap_apply,hc,sourceSignedGapSequence_apply,sub_re,hχ.2 n,ofReal_re]
  exact sub_nonpos.mpr hν.1

/-- Global signed-gap injectivity would prove actual Hilbert squared-gap spectral uniqueness.
This reduction retains the intrinsic periodic spectrum and all algebraic multiplicities. -/
theorem source_isospectral_of_squared_gaps_of_symmetricSignedGap_injective
    (hinj : Function.Injective (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)))
    (φ ψ : realTypeSourceSubmodule 2)
    (hgaps : ∀ n,
      (canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val) (periodOnePotential_mem _) n)^2 =
      (canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential ψ.val) (periodOnePotential_mem _) n)^2) :
    ψ ∈ sourceIsospectralSet (by simp) φ := by
  obtain ⟨a,ha,ha0⟩ := exists_symmetric_coordinates_isospectral_nonpos_signed_gaps φ
  obtain ⟨b,hb,hb0⟩ := exists_symmetric_coordinates_isospectral_nonpos_signed_gaps ψ
  have htransport (θ : realTypeSourceSubmodule 2) (c : RealCoeff 2)
      (hc : symmetricRealSourceCoefficients 2 c ∈ sourceIsospectralSet (by simp) θ) (n : ℤ) :
      (sourceSignedGapSequence (by simp) (by norm_num) (symmetricSourceCoefficients 2 c) n)^2 =
        (canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential θ.val) (periodOnePotential_mem _) n)^2 := by
    have hs := sourceSignedGapSequence_sq_of_reflection_fixed (by simp) (by norm_num)
      (symmetricRealSourceCoefficients 2 c) (symmetricRealSourceCoefficients_reflection_fixed c) n
    simp only [symmetricRealSourceCoefficients_val] at hs
    rw [hs]
    have he := canonicalPeriodicEndpoints_eq_of_spectral_data (by simp) (by norm_num)
      (periodOnePotential (symmetricSourceCoefficients 2 c)) (periodOnePotential θ.val)
      (periodOnePotential_mem _) (periodOnePotential_mem _) hc.1 hc.2
    simp only [canonicalPeriodicGap,he.1,he.2]
  have hab : a = b := by
    apply hinj
    ext n
    have he := (htransport φ a ha n).trans ((hgaps n).trans (htransport ψ b hb n).symm)
    have hima := sourceSignedGapSequence_im_eq_zero (by simp) (by norm_num)
      (symmetricRealSourceCoefficients 2 a) n
    have himb := sourceSignedGapSequence_im_eq_zero (by simp) (by norm_num)
      (symmetricRealSourceCoefficients 2 b) n
    simp only [symmetricRealSourceCoefficients_val] at hima himb
    have hr := congrArg Complex.re he
    simp only [pow_two,mul_re,hima,himb,mul_zero,sub_zero] at hr
    change symmetricSourceSignedGapMap (by simp) (by norm_num) a n *
      symmetricSourceSignedGapMap (by simp) (by norm_num) a n =
      symmetricSourceSignedGapMap (by simp) (by norm_num) b n *
      symmetricSourceSignedGapMap (by simp) (by norm_num) b n at hr
    nlinarith [ha0 n,hb0 n]
  subst b
  exact ⟨hb.1.symm.trans ha.1,fun z => (hb.2 z).symm.trans (ha.2 z)⟩

end NLS.ZakharovShabat
