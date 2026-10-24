import NLS.SequenceSpaces.HilbertMatrixTranspose
import NLS.FunctionalAnalysis.CompactDenseRange

/-! # The transpose criterion for compact Hilbert matrices

For a compact perturbation of a nonzero scalar identity, vanishing of
the ordinary transpose kernel forces dense range and hence bijectivity.
This bridges a transpose-oriented matrix calculation to the original
bounded operator without identifying the two matrices.
-/
noncomputable section
namespace NLS.Coeff

/-- A compact scalar perturbation with injective transpose is bijective. -/
theorem bijective_of_injective_hilbertMatrixTranspose_compact_sub_smul
    (A : Coeff 2 →L[ℂ] Coeff 2) {c : ℂ} (hc : c ≠ 0)
    (hA : IsCompactOperator (A - c • 1 : Coeff 2 →L[ℂ] Coeff 2))
    (ht : Function.Injective (hilbertMatrixTranspose A)) : Function.Bijective A := by
  have hd := (injective_hilbertMatrixTranspose_iff_denseRange A).mp ht
  let M : Coeff 2 →L[ℂ] Coeff 2 := c⁻¹ • 1
  have hm : Function.Surjective M := by
    intro y
    refine ⟨c • y, ?_⟩
    change c⁻¹ • (c • y) = y
    exact inv_smul_smul₀ hc y
  have hdn : DenseRange (c⁻¹ • A : Coeff 2 →L[ℂ] Coeff 2) :=
    hm.denseRange.comp hd M.continuous
  have hcn : IsCompactOperator (c⁻¹ • A - 1 : Coeff 2 →L[ℂ] Coeff 2) := by
    have he : c⁻¹ • (A - c • 1) = c⁻¹ • A - 1 := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hc, one_smul]
    exact he ▸ hA.smul c⁻¹
  have hn := NLS.CompactSpectrum.bijective_of_denseRange_compact_sub_id
    (c⁻¹ • A) hcn hdn
  apply NLS.CompactSpectrum.bijective_of_injective_compact_sub_smul A hc hA
  intro x y hxy
  apply hn.1
  exact congrArg (fun z => c⁻¹ • z) hxy

end NLS.Coeff
