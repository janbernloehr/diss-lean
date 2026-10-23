import NLS.ZakharovShabat.SymmetricSignedGapLocalInverse
import NLS.ZakharovShabat.SourceSpectralSequenceCompactDerivative

/-! # Compact perturbation of the symmetric signed-gap derivative

On the actual reflection-fixed slice the signed gap is twice the difference
between the Dirichlet root and the periodic midpoint. The full sequence derivative therefore
differs from twice the identity by a compact operator at every Hilbert
source in this slice. Injectivity of these derivatives is a separate issue.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The opposite-endpoint identity, as an equality of full coefficient sequences. -/
theorem sourceSignedGapSequence_eq_twice_dirichlet_sub_midpoint
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (hφ : realSourceSpatialReflection φ = φ) :
    sourceSignedGapSequence hp hp1 φ.val = (2 : ℝ) •
      (sourceBoundaryDisplacement hp hp1 .dirichlet φ.val -
        sourcePeriodicMidpointDisplacement hp hp1 φ.val) := by
  ext n
  simp only [sourceSignedGapSequence_apply, lp.coeFn_smul, Pi.smul_apply,
    lp.coeFn_sub, Pi.sub_apply, sourceBoundaryDisplacement_apply,
    sourcePeriodicMidpointDisplacement_apply, canonicalPeriodicMidpoint]
  rcases sourceBoundaryRoots_opposite_endpoints_of_reflection_fixed hp hp1 φ hφ n with h | h
  · rw [h.1,h.2]
    simp only [real_smul, ofReal_ofNat]
    ring
  · rw [h.1,h.2]
    simp only [real_smul, ofReal_ofNat]
    ring

private def symmetricSpectralRealDerivative (T : CoeffPair 2 →L[ℂ] Coeff 2) :
    RealCoeff 2 →L[ℝ] RealCoeff 2 :=
  (Coeff.reCLM 2).comp ((T.restrictScalars ℝ).comp (symmetricSourceCoefficients 2))

private theorem symmetricSpectralRealDerivative_sub
    (A B : CoeffPair 2 →L[ℂ] Coeff 2) :
    symmetricSpectralRealDerivative (A-B) =
      symmetricSpectralRealDerivative A - symmetricSpectralRealDerivative B := by
  ext h n
  rfl

private theorem compact_symmetricSpectralRealDerivative
    (T : CoeffPair 2 →L[ℂ] Coeff 2) (hT : IsCompactOperator T) :
    IsCompactOperator (symmetricSpectralRealDerivative T) := by
  exact (hT.comp_clm (symmetricSourceCoefficients 2)).clm_comp (Coeff.reCLM 2)

private theorem fderiv_symmetricSourceSignedGapMap_formula (a : RealCoeff 2) :
    fderiv ℝ (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) a =
      (2 : ℝ) • symmetricSpectralRealDerivative
        (fderiv ℂ (sourceBoundaryDisplacement (p := 2) (by simp) (by norm_num) .dirichlet)
          (symmetricSourceCoefficients 2 a) -
         fderiv ℂ (sourcePeriodicMidpointDisplacement (p := 2) (by simp) (by norm_num))
          (symmetricSourceCoefficients 2 a)) := by
  let S := symmetricSourceCoefficients 2
  let D := sourceBoundaryDisplacement (p := 2) (by simp) (by norm_num) .dirichlet
  let M := sourcePeriodicMidpointDisplacement (p := 2) (by simp) (by norm_num)
  obtain ⟨_,_,hrealD,hD⟩ := exists_sourceBoundaryDisplacement_analytic_common_domain
    (p := 2) (by simp) (by norm_num)
  obtain ⟨_,_,hrealM,hM⟩ := exists_sourcePeriodicMidpointDisplacement_analytic_common_domain
    (p := 2) (by simp) (by norm_num)
  have hd := (hD .dirichlet (S a) (hrealD (symmetricSourceCoefficients_realType a))).differentiableAt.hasFDerivAt
  have hm := (hM (S a) (hrealM (symmetricSourceCoefficients_realType a))).differentiableAt.hasFDerivAt
  have hpre := ((hd.sub hm).restrictScalars ℝ).comp a S.hasFDerivAt
  have hpost := ((Coeff.reCLM 2).hasFDerivAt.comp a hpre).const_smul (2 : ℝ)
  have he : symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num) =
      fun b => (2 : ℝ) • Coeff.reCLM 2 (D (S b) - M (S b)) := by
    funext b
    unfold symmetricSourceSignedGapMap
    have hb := sourceSignedGapSequence_eq_twice_dirichlet_sub_midpoint
      (by simp) (by norm_num) (symmetricRealSourceCoefficients 2 b)
      (symmetricRealSourceCoefficients_reflection_fixed b)
    simp only [symmetricRealSourceCoefficients_val] at hb
    rw [hb, map_smul]
  rw [he]
  exact hpost.fderiv

/-- At every symmetric real Hilbert source the actual signed-gap derivative is twice the
identity plus a compact operator. This does not assert injectivity of that derivative. -/
theorem isCompactOperator_fderiv_symmetricSourceSignedGapMap_sub_two_id (a : RealCoeff 2) :
    IsCompactOperator
      (fderiv ℝ (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) a -
        (2 : ℝ) • ContinuousLinearMap.id ℝ (RealCoeff 2)) := by
  let S := symmetricSourceCoefficients 2
  let D := sourceBoundaryDisplacement (p := 2) (by simp) (by norm_num) .dirichlet
  let M := sourcePeriodicMidpointDisplacement (p := 2) (by simp) (by norm_num)
  have ha := source_spectral_sequence_derivatives_compact_of_realType
    (S a) (symmetricSourceCoefficients_realType a)
  have hz := source_spectral_sequence_derivatives_compact_of_realType
    0 (by simp [IsRealType])
  have hc := (compact_symmetricSpectralRealDerivative
    ((fderiv ℂ D (S a) - fderiv ℂ D 0) - (fderiv ℂ M (S a) - fderiv ℂ M 0))
    (ha.2.sub (ha.1.sub hz.1))).smul (2 : ℝ)
  have he : fderiv ℝ (symmetricSourceSignedGapMap (p := 2) (by simp) (by norm_num)) a -
      (2 : ℝ) • ContinuousLinearMap.id ℝ (RealCoeff 2) =
      (2 : ℝ) • symmetricSpectralRealDerivative
        ((fderiv ℂ D (S a) - fderiv ℂ D 0) - (fderiv ℂ M (S a) - fderiv ℂ M 0)) := by
    rw [← hasFDerivAt_symmetricSourceSignedGapMap_zero.fderiv,
      fderiv_symmetricSourceSignedGapMap_formula a,
      fderiv_symmetricSourceSignedGapMap_formula 0]
    simp only [map_zero, symmetricSpectralRealDerivative_sub, smul_sub]
    dsimp only [D,M,S]
    abel
  rw [he]
  exact hc

end NLS.ZakharovShabat
