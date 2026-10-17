import NLS.ZakharovShabat.SourceBirkhoffWeightedJacobianCompact
import NLS.ZakharovShabat.SourceBirkhoffWeightedJacobianInjective

/-! # Bijectivity of the full native weighted Jacobian

The Fredholm alternative applies to the normalized compact perturbation
of the free Fourier equivalence. The previously proved trivial kernel
then gives surjectivity. Transport through the weight coordinates returns
bijectivity of the actual derivative in its native weighted spaces.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
private theorem bijective_of_compact_sub_equiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E →L[ℂ] F) (Q : E ≃L[ℂ] F)
    (hC : IsCompactOperator (T-Q.toContinuousLinearMap)) (hi : Function.Injective T) :
    Function.Bijective T := by
  let M := Q.symm.toContinuousLinearMap.comp T
  have hMc : IsCompactOperator (M-ContinuousLinearMap.id ℂ E) := by
    have he : M-ContinuousLinearMap.id ℂ E = Q.symm.toContinuousLinearMap.comp (T-Q.toContinuousLinearMap) := by
      ext x
      change Q.symm (T x)-x = Q.symm (T x-Q x)
      rw [map_sub,ContinuousLinearEquiv.symm_apply_apply]
    rw [he]
    exact hC.clm_comp Q.symm.toContinuousLinearMap
  have hMi : Function.Injective M := Q.symm.injective.comp hi
  have hMb : Function.Bijective M := CompactSpectrum.bijective_of_injective_compact_sub_smul M one_ne_zero
    (by simpa using hMc) hMi
  refine ⟨hi,fun y => ?_⟩
  obtain ⟨x,hx⟩ := hMb.2 (Q.symm y)
  exact ⟨x,Q.symm.injective hx⟩

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual native complex weighted Jacobian is bijective at every weighted real source. -/
theorem originalWeightedBirkhoffMap_fderiv_bijective
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    Function.Bijective (fderiv ℂ (originalWeightedBirkhoffMap hp hp1 s w) a.val) := by
  have hi := D.originalWeightedBirkhoffMap_fderiv_injective w a
  have hBi : Function.Injective (normalizedWeightedBirkhoffJacobian hp hp1 s w a.val) :=
    (CoeffPair.toMax p).injective.comp ((sourcePairWeightCoordinates w).injective.comp
      (hi.comp (sourcePairWeightCoordinates w).symm.injective))
  have hB := bijective_of_compact_sub_equiv (normalizedWeightedBirkhoffJacobian hp hp1 s w a.val)
    sourceBirkhoffFourierEquiv (D.isCompactOperator_normalizedWeightedBirkhoffJacobian_sub_fourier_real w a) hBi
  refine ⟨hi,fun y => ?_⟩
  obtain ⟨v,hv⟩ := hB.2 (CoeffPair.toMax p (sourcePairWeightCoordinates w y))
  refine ⟨(sourcePairWeightCoordinates w).symm v,?_⟩
  apply (sourcePairWeightCoordinates w).injective
  apply (CoeffPair.toMax p).injective
  exact hv
end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
