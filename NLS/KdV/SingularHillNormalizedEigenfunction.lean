import NLS.KdV.SingularHillPhysicalPairing

/-! Actual full-domain periodic eigenfunctions, normalized in the exact
source periodic L2 norm, for arbitrary original complex H-minus-one data. -/
noncomputable section
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

/-- Every actual spectral value has a native H1 eigenfunction of source
L2 norm ONE. Its physical norm-square HALF-integral is exactly one. -/
theorem exists_singularHill_normalized_eigenfunction
    (q : FourierLebesgueSpace (2:ℝ) (-1) 2) (lambda : ℂ)
    (hl : lambda ∈ singularHillSpectrum q) :
    ∃ g : FourierLebesgueSpace (2:ℝ) 1 2,
      singularHillOperator q g = lambda • singularHillDomainInclusion g ∧
      ‖singularHillL2DomainInclusion g‖ = 1 ∧
      (1/2:ℝ) * (∫ x in (0:ℝ)..2,
        ‖circlePullback (singularHillL2DomainInclusion g) x‖^2) = 1 := by
  obtain ⟨f,hf0,hf⟩ := (mem_singularHillSpectrum_iff q lambda).mp hl
  have hfL2 : singularHillL2DomainInclusion f ≠ 0 := by
    intro he
    exact hf0 (singularHillL2DomainInclusion_injective (by simpa only [map_zero] using he))
  have hn : ‖singularHillL2DomainInclusion f‖ ≠ 0 := norm_ne_zero_iff.mpr hfL2
  let a : ℂ := ((‖singularHillL2DomainInclusion f‖)⁻¹:ℝ)
  let g := a • f
  have hg : ‖singularHillL2DomainInclusion g‖ = 1 := by
    rw [show g = a • f from rfl,map_smul,norm_smul]
    dsimp [a]
    rw [Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),inv_mul_cancel₀ hn]
  refine ⟨g,?_,hg,?_⟩
  · change singularHillOperator q (a • f) = lambda • singularHillDomainInclusion (a • f)
    rw [map_smul,map_smul,hf,smul_smul,smul_smul,mul_comm a lambda]
  · rw [← norm_sq_singularHillPhysicalL2,hg,one_pow]

end NLS.KdV
