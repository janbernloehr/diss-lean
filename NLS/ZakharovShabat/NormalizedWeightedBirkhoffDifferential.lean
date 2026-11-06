import NLS.ZakharovShabat.SourceBirkhoffWeightedJacobianCompact

/-! # The ACTUAL normalized weighted map has its verified compact Fourier jet

The derivative of the existing normalized weighted map is EXACTLY the
actual native Jacobian transported through its weight coordinates.
The verified canonical Fourier-plus-compact theorem therefore applies
to this same map at EVERY normalized real source and spectral weight.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

private theorem fderiv_linear_conjugation
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (I : E ≃L[ℂ] F) (L : F →L[ℂ] G) (f : E → E) (g : F → G) (a : E)
    (hf : DifferentiableAt ℂ f a)
    (he : ∀ x, g x=L (I (f (I.symm x)))) :
    fderiv ℂ g (I a)=L.comp (I.toContinuousLinearMap.comp
      ((fderiv ℂ f a).comp I.symm.toContinuousLinearMap)) := by
  have hf' : HasFDerivAt f (fderiv ℂ f a) (I.symm (I a)) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hf.hasFDerivAt
  have hd := L.hasFDerivAt.comp (I a) (I.hasFDerivAt.comp (I a)
    (hf'.comp (I a) I.symm.hasFDerivAt))
  have hfun : g=(fun x => L (I (f (I.symm x)))) := funext he
  rw [hfun]
  exact hd.fderiv

variable {p : ℝ≥0∞} [Fact (1≤p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p≠⊤} {hp1 : 1<p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The derivative of the SAME actual normalized weighted map is its
previously verified native weighted Jacobian in normalized coordinates. -/
theorem fderiv_normalizedWeightedBirkhoffMap_eq
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p) (ha : a∈D.originalWeightedComplexDomain w) :
    fderiv ℂ (normalizedWeightedBirkhoffMap hp hp1 s w) (sourcePairWeightCoordinates w a)=
      normalizedWeightedBirkhoffJacobian hp hp1 s w a := by
  apply fderiv_linear_conjugation (sourcePairWeightCoordinates w).toContinuousLinearEquiv
    (CoeffPair.toMax p).toContinuousLinearMap (originalWeightedBirkhoffMap hp hp1 s w)
    (normalizedWeightedBirkhoffMap hp hp1 s w) a
    ((D.originalWeightedComplexDomain_spec w).2.2.1 a ha).differentiableAt
  intro ψ
  change normalizedWeightedBirkhoffMap hp hp1 s w ψ=
    (CoeffPair.toMax p) (sourcePairWeightCoordinates w
      ((sourcePairWeightCoordinates w).symm ((CoeffPair.toMax p).symm
        (normalizedWeightedBirkhoffMap hp hp1 s w
          (sourcePairWeightCoordinates w ((sourcePairWeightCoordinates w).symm ψ))))))
  simp only [LinearIsometryEquiv.apply_symm_apply,ContinuousLinearEquiv.apply_symm_apply]

/-- EVERY normalized actual real source has the ACTUAL weighted map
Fourier derivative plus a compact remainder, for EVERY spectral weight. -/
theorem isCompactOperator_fderiv_normalizedWeightedBirkhoffMap_sub_fourier
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (φ : realTypeSourceLocus p) :
    IsCompactOperator (fderiv ℂ (normalizedWeightedBirkhoffMap hp hp1 s w) φ.val-sourceBirkhoffFourier (p := p)) := by
  let a := (weightedRealSourceEquiv (p := p) w).symm (⟨φ.val,φ.property⟩ : realTypeSourceSubmodule p)
  have ha : sourcePairWeightCoordinates w a.val=φ.val := by
    exact congrArg (fun b : realTypeSourceSubmodule p => b.val)
      ((weightedRealSourceEquiv (p := p) w).apply_symm_apply ⟨φ.val,φ.property⟩)
  have hd := D.fderiv_normalizedWeightedBirkhoffMap_eq w a.val
    ((D.originalWeightedComplexDomain_spec w).2.1 a)
  rw [ha] at hd
  rw [hd]
  exact D.isCompactOperator_normalizedWeightedBirkhoffJacobian_sub_fourier_real w a

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
