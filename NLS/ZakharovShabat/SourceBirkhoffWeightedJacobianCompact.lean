import NLS.ZakharovShabat.SourceBirkhoffWeightedFiniteGapJacobianCompact
import NLS.ZakharovShabat.SourceWeightedFiniteGapDensity

/-! # Compact weighted Birkhoff remainders at every real source

The actual normalized weighted Jacobian varies continuously in the
weighted real topology. Finite-gap density and closedness of the compact
operators extend the finite-gap Fourier remainder to every real source.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The normalized weighted Jacobian is continuous on the entire weighted real source space. -/
theorem continuous_normalizedWeightedBirkhoffJacobian_real
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight) :
    Continuous (fun a : weightedRealSourceSubmodule (p := p) w =>
      normalizedWeightedBirkhoffJacobian hp hp1 s w a.val) := by
  have hA := (D.originalWeightedComplexDomain_spec w).2.2.1.fderiv
  have hd : Continuous (fun a : weightedRealSourceSubmodule (p := p) w =>
      fderiv ℂ (originalWeightedBirkhoffMap hp hp1 s w) a.val) := by
    apply continuous_iff_continuousAt.mpr
    intro a
    exact (hA a.val ((D.originalWeightedComplexDomain_spec w).2.1 a)).continuousAt.comp
      continuous_subtype_val.continuousAt
  unfold normalizedWeightedBirkhoffJacobian
  exact continuous_const.clm_comp (continuous_const.clm_comp (hd.clm_comp continuous_const))

private theorem closed_property_of_dense
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (S : Set X) (hd : Dense S) (f : X → Y) (hf : Continuous f)
    (C : Set Y) (hc : IsClosed C) (h : ∀ x ∈ S, f x ∈ C) (x : X) : f x ∈ C :=
  closure_minimal h (hc.preimage hf) (hd x)

/-- At every weighted real source, the normalized Jacobian differs compactly from the Fourier map. -/
theorem isCompactOperator_normalizedWeightedBirkhoffJacobian_sub_fourier_real
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    IsCompactOperator (normalizedWeightedBirkhoffJacobian hp hp1 s w a.val-sourceBirkhoffFourier (p := p)) := by
  let e := weightedRealSourceEquiv (p := p) w
  have hfinite (b : realTypeSourceSubmodule p)
      (hb : normalizedWeightedRealSourceLp w b ∈ sourceFiniteGapLocus hp hp1) :
      originalWeightedRealSource w (e.symm b) ∈ sourceFiniteGapLocus hp hp1 := by
    change normalizedWeightedRealSourceLp w (e (e.symm b)) ∈ sourceFiniteGapLocus hp hp1
    rwa [ContinuousLinearEquiv.apply_symm_apply]
  have h := closed_property_of_dense _ (dense_normalizedWeightedRealSource_finiteGap hp hp1 w)
    (fun b : realTypeSourceSubmodule p =>
      normalizedWeightedBirkhoffJacobian hp hp1 s w (e.symm b).val-sourceBirkhoffFourier (p := p))
    (((D.continuous_normalizedWeightedBirkhoffJacobian_real w).comp e.symm.continuous).sub continuous_const)
    {T : CoeffPair p →L[ℂ] (Coeff p × Coeff p) | IsCompactOperator T}
    isClosed_setOfPred_isCompactOperator
    (fun b hb => D.isCompactOperator_normalizedWeightedBirkhoffJacobian_sub_fourier_finiteGap w (e.symm b) (hfinite b hb))
    (e a)
  simpa only [ContinuousLinearEquiv.symm_apply_apply,Set.mem_ofPred_eq] using h
end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
