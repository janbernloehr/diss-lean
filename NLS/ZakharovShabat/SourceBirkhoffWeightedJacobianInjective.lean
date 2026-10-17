import NLS.ZakharovShabat.SourceBirkhoffWeightedComplexDomain
import NLS.ZakharovShabat.SourceBirkhoffJacobianAllExponents

/-! # Injectivity of the actual weighted Jacobian

Compatibility with the unweighted bijective derivative kills every weighted
kernel vector. Surjectivity in the stronger weighted topology is separate.
-/

noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The full weighted Jacobian has trivial kernel at every real source. -/
theorem SourceBirkhoffMapComplexData.originalWeightedBirkhoffMap_fderiv_injective
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    Function.Injective (fderiv ℂ (originalWeightedBirkhoffMap hp hp1 s w) a.val) := by
  have hspec := D.originalWeightedComplexDomain_spec w
  have hc := hspec.2.2.2 a.val (hspec.2.1 a)
  have hi := (D.jacobian_bijective_all_exponents (originalWeightedRealSource w a)).1
  apply (injective_iff_map_eq_zero (fderiv ℂ (originalWeightedBirkhoffMap hp hp1 s w) a.val)).mpr
  intro v hv
  apply originalWeightedSourceCLM_injective w
  rw [map_zero]
  apply (injective_iff_map_eq_zero _).mp hi
  have h := congrArg (fun L => L v) hc.2.2
  simp only [ContinuousLinearMap.comp_apply,hv,map_zero] at h
  exact h.symm
end NLS.ZakharovShabat
