import NLS.MKdV.MiuraSobolevNLSCoordinates
import NLS.ZakharovShabat.SourceBirkhoffWeightedJacobianCompact
import NLS.MKdV.MiuraCartesianJacobianCompact

/-! # Compact native Sobolev NLS derivative remainders on the scalar diagonal

Normalization of the actual weighted derivative commutes with the scalar
diagonal. The verified weighted NLS compact remainder therefore applies
in the original scalar H^s norm, at every real profile and integer order.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraSobolevNLSNormalizedInput (s : ℕ) : ScalarSobolev s →L[ℂ] CoeffPair 2 :=
  (sourcePairWeightCoordinates (miuraActionFlowWeight s)).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (miuraSobolevNLSInput s)

theorem hasFDerivAt_miuraSobolevNLSNormalizedCoordinates (s : ℕ) (a : ScalarSobolev s)
    (ha : ∀ j, a.val j = conj (a.val (-j))) :
    HasFDerivAt (miuraSobolevNLSNormalizedCoordinates s)
      ((normalizedWeightedBirkhoffJacobian (by simp) (by norm_num) miuraActionFlowFamily.psi
        (miuraActionFlowWeight s) (miuraSobolevNLSInput s a)).comp (miuraSobolevNLSNormalizedInput s)) a := by
  let D := miuraActionFlowFamily.data
  have hr : miuraSobolevNLSInput s a ∈ weightedRealSourceSubmodule (miuraActionFlowWeight s) := by
    apply (mem_weightedRealSourceSubmodule_iff _ _).mpr
    intro j
    rw [miuraSobolevNLSInput_snd,miuraSobolevNLSInput_fst]
    exact ha j
  have hA := (D.originalWeightedComplexDomain_spec (miuraActionFlowWeight s)).2.2.1 _
    ((D.originalWeightedComplexDomain_spec (miuraActionFlowWeight s)).2.1 ⟨_,hr⟩)
  let T := (CoeffPair.toMax 2).toContinuousLinearMap.comp
    (sourcePairWeightCoordinates (miuraActionFlowWeight s)).toContinuousLinearEquiv.toContinuousLinearMap
  have hd := T.hasFDerivAt.comp a
    (hA.differentiableAt.hasFDerivAt.comp a (miuraSobolevNLSInput s).hasFDerivAt)
  have he : T.comp ((fderiv ℂ (originalWeightedBirkhoffMap (by simp) (by norm_num)
      miuraActionFlowFamily.psi (miuraActionFlowWeight s)) (miuraSobolevNLSInput s a)).comp
        (miuraSobolevNLSInput s)) =
      (normalizedWeightedBirkhoffJacobian (by simp) (by norm_num) miuraActionFlowFamily.psi
        (miuraActionFlowWeight s) (miuraSobolevNLSInput s a)).comp (miuraSobolevNLSNormalizedInput s) := by
    apply ContinuousLinearMap.ext
    intro h
    dsimp only [T,normalizedWeightedBirkhoffJacobian,miuraSobolevNLSNormalizedInput,
      ContinuousLinearMap.comp_apply]
    congr 2
    exact congrArg (fderiv ℂ (originalWeightedBirkhoffMap (by simp) (by norm_num)
      miuraActionFlowFamily.psi (miuraActionFlowWeight s)) (miuraSobolevNLSInput s a))
        ((sourcePairWeightCoordinates (miuraActionFlowWeight s)).symm_apply_apply (miuraSobolevNLSInput s h)).symm
  change HasFDerivAt (miuraSobolevNLSNormalizedCoordinates s) _ a at hd
  rw [he] at hd
  exact hd

theorem isCompactOperator_fderiv_miuraSobolevNLSNormalizedCoordinates_sub_free
    (s : ℕ) (a : ScalarSobolev s) (ha : ∀ j, a.val j = conj (a.val (-j))) :
    IsCompactOperator (fderiv ℂ (miuraSobolevNLSNormalizedCoordinates s) a-
      fderiv ℂ (miuraSobolevNLSNormalizedCoordinates s) 0) := by
  let D := miuraActionFlowFamily.data
  have hr : miuraSobolevNLSInput s a ∈ weightedRealSourceSubmodule (miuraActionFlowWeight s) := by
    apply (mem_weightedRealSourceSubmodule_iff _ _).mpr
    intro j
    rw [miuraSobolevNLSInput_snd,miuraSobolevNLSInput_fst]
    exact ha j
  have hc := D.isCompactOperator_normalizedWeightedBirkhoffJacobian_sub_fourier_real
    (miuraActionFlowWeight s) ⟨_,hr⟩
  have h0 := D.isCompactOperator_normalizedWeightedBirkhoffJacobian_sub_fourier_real
    (miuraActionFlowWeight s) 0
  have hzero : ∀ j : ℤ, (0 : ScalarSobolev s).val j = conj ((0 : ScalarSobolev s).val (-j)) := by
    intro j
    simp
  rw [(hasFDerivAt_miuraSobolevNLSNormalizedCoordinates s a ha).fderiv,
    (hasFDerivAt_miuraSobolevNLSNormalizedCoordinates s 0 hzero).fderiv,← ContinuousLinearMap.sub_comp]
  have he : (normalizedWeightedBirkhoffJacobian (by simp) (by norm_num) miuraActionFlowFamily.psi
      (miuraActionFlowWeight s) (miuraSobolevNLSInput s a)-sourceBirkhoffFourier)-
      (normalizedWeightedBirkhoffJacobian (by simp) (by norm_num) miuraActionFlowFamily.psi
        (miuraActionFlowWeight s) 0-sourceBirkhoffFourier) =
      normalizedWeightedBirkhoffJacobian (by simp) (by norm_num) miuraActionFlowFamily.psi
        (miuraActionFlowWeight s) (miuraSobolevNLSInput s a)-
      normalizedWeightedBirkhoffJacobian (by simp) (by norm_num) miuraActionFlowFamily.psi
        (miuraActionFlowWeight s) 0 := by abel
  have h := hc.sub h0
  change IsCompactOperator (((normalizedWeightedBirkhoffJacobian (by simp) (by norm_num)
      miuraActionFlowFamily.psi (miuraActionFlowWeight s) (miuraSobolevNLSInput s a)-sourceBirkhoffFourier)-
      (normalizedWeightedBirkhoffJacobian (by simp) (by norm_num) miuraActionFlowFamily.psi
        (miuraActionFlowWeight s) 0-sourceBirkhoffFourier) : CoeffPair 2 →L[ℂ] (Coeff 2 × Coeff 2))) at h
  rw [he] at h
  simpa only [map_zero] using! h.comp_clm (miuraSobolevNLSNormalizedInput s)

theorem miuraSobolevNLSNormalizedCoordinates_zero (s : ℕ) :
    miuraSobolevNLSNormalizedCoordinates s 0 = 0 := by
  have hzero : ∀ j : ℤ, (0 : ScalarSobolev s).val j = conj ((0 : ScalarSobolev s).val (-j)) := by
    intro j
    simp
  obtain ⟨U,_,hr,_,hc⟩ := exists_miuraSobolevNLSNormalizedCoordinates_domain s
  have hz := miuraActionFlowFamily.data.birkhoff_map_zero
  apply Prod.ext <;> ext n
  · rw [(hc 0 (hr hzero) n).1,map_zero,hz]
    simp
  · rw [(hc 0 (hr hzero) n).2,map_zero,hz]
    simp

end NLS.MKdV
