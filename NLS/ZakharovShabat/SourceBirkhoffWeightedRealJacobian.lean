import NLS.ZakharovShabat.SourceWeightedRealInclusion
import NLS.ZakharovShabat.SourceBirkhoffWeightedLocalInverse
import NLS.ZakharovShabat.SourceBirkhoffWeightedRealAnalytic
import NLS.ZakharovShabat.SourceBirkhoffProposition17_1

/-! # The actual native weighted real Jacobian

Differentiating the actual complex inclusion identifies the real derivative.
The bounded complex inverse preserves the weighted real form, by compatibility
with the unweighted inverse. This constructs a bounded real equivalence.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- The actual real weighted map is the real restriction of its complex extension. -/
theorem originalWeightedRealMap_complex_inclusion
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    WeightedCoeffPair.complexCLM (sourceFrequencyWeight w) (D.originalWeightedRealMap w a) =
      originalWeightedBirkhoffMap hp hp1 s w a.val := by
  apply (WithLp.equiv p _).injective
  apply Prod.ext <;> apply Subtype.ext <;> funext n
  · exact (D.originalWeightedBirkhoffMap_real w a n).1.symm
  · exact (D.originalWeightedBirkhoffMap_real w a n).2.symm

/-- Differentiation commutes with inclusion of the native weighted real forms. -/
theorem originalWeightedRealMap_fderiv_complex_inclusion
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a v : weightedRealSourceSubmodule (p := p) w) :
    WeightedCoeffPair.complexCLM (sourceFrequencyWeight w) (fderiv ℝ (D.originalWeightedRealMap w) a v) =
      fderiv ℂ (originalWeightedBirkhoffMap hp hp1 s w) a.val v.val := by
  let inc := WeightedCoeffPair.complexCLM (p := p) (sourceFrequencyWeight w)
  have hl := inc.hasFDerivAt.comp a
    (D.originalWeightedRealMap_analytic w a (mem_univ a)).differentiableAt.hasFDerivAt
  have ha := (D.originalWeightedComplexDomain_spec w).2.2.1 a.val
    ((D.originalWeightedComplexDomain_spec w).2.1 a)
  have hr := (ha.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp a
    (weightedRealSourceSubmodule (p := p) w).subtypeL.hasFDerivAt
  have he : (fun b => inc (D.originalWeightedRealMap w b)) =
      fun b : weightedRealSourceSubmodule (p := p) w => originalWeightedBirkhoffMap hp hp1 s w b.val :=
    funext (D.originalWeightedRealMap_complex_inclusion w)
  change HasFDerivAt (fun b => inc (D.originalWeightedRealMap w b)) _ a at hl
  rw [he] at hl
  exact congrArg (fun L => L v) (hl.unique hr)

/-- The bounded complex inverse Jacobian preserves the native weighted real forms. -/
theorem originalWeightedJacobianEquiv_symm_real
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w)
    (z : WithLp p (WeightedRealCoeff (sourceFrequencyWeight w) p × WeightedRealCoeff (sourceFrequencyWeight w) p)) :
    (D.originalWeightedJacobianEquiv w a).symm (WeightedCoeffPair.complexCLM (sourceFrequencyWeight w) z) ∈
      weightedRealSourceSubmodule w := by
  let φ := originalWeightedRealSource w a
  let y := originalWeightedRealTarget w z
  let u := (D.realJacobianEquivAll φ).symm y
  have hu : (D.jacobianEquivAll φ).symm
      (((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p)) y) = u.val := by
    apply (D.jacobianEquivAll φ).injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    change _ = sourceBirkhoffJacobian hp hp1 s φ.val u.val
    rw [← D.real_jacobian_complex_inclusion φ u]
    change _ = ((RealCoeff.complexCLM p).prodMap (RealCoeff.complexCLM p))
      (D.realJacobianEquivAll φ ((D.realJacobianEquivAll φ).symm y))
    rw [ContinuousLinearEquiv.apply_symm_apply]
  apply (originalWeightedSourceCLM_mem_real_iff w _).mp
  have h := congrArg (fun L => L (WeightedCoeffPair.complexCLM (sourceFrequencyWeight w) z))
    (D.originalWeightedJacobianEquiv_symm_forget w a)
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,weightedBirkhoffTargetInclusion_complexCLM] at h
  rw [h,hu]
  exact u.property

/-- The actual real weighted derivative is bijective at every weighted real source. -/
theorem originalWeightedRealMap_fderiv_bijective
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    Function.Bijective (fderiv ℝ (D.originalWeightedRealMap w) a) := by
  constructor
  · intro u v huv
    apply Subtype.ext
    apply (D.originalWeightedBirkhoffMap_fderiv_bijective w a).1
    rw [← D.originalWeightedRealMap_fderiv_complex_inclusion w a u,
      ← D.originalWeightedRealMap_fderiv_complex_inclusion w a v,huv]
  · intro z
    let v := (D.originalWeightedJacobianEquiv w a).symm (WeightedCoeffPair.complexCLM (sourceFrequencyWeight w) z)
    let u : weightedRealSourceSubmodule (p := p) w := ⟨v,D.originalWeightedJacobianEquiv_symm_real w a z⟩
    refine ⟨u,?_⟩
    apply WeightedCoeffPair.complexCLM_injective
    rw [D.originalWeightedRealMap_fderiv_complex_inclusion]
    exact (D.originalWeightedJacobianEquiv w a).apply_symm_apply _

/-- The actual real weighted Jacobian as a bounded real linear equivalence. -/
def originalWeightedRealJacobianEquiv
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    weightedRealSourceSubmodule (p := p) w ≃L[ℝ]
      WithLp p (WeightedRealCoeff (sourceFrequencyWeight w) p × WeightedRealCoeff (sourceFrequencyWeight w) p) :=
  ContinuousLinearEquiv.ofBijective (fderiv ℝ (D.originalWeightedRealMap w) a)
    (LinearMap.ker_eq_bot.mpr (D.originalWeightedRealMap_fderiv_bijective w a).1)
    (LinearMap.range_eq_top.mpr (D.originalWeightedRealMap_fderiv_bijective w a).2)

/-- The constructed equivalence is the actual real derivative. -/
@[simp] theorem originalWeightedRealJacobianEquiv_toContinuousLinearMap
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    (D.originalWeightedRealJacobianEquiv w a).toContinuousLinearMap =
      fderiv ℝ (D.originalWeightedRealMap w) a := rfl

/-- The real inverse Jacobian is the restriction of the complex inverse Jacobian. -/
theorem originalWeightedRealJacobianEquiv_symm_complex
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w)
    (z : WithLp p (WeightedRealCoeff (sourceFrequencyWeight w) p × WeightedRealCoeff (sourceFrequencyWeight w) p)) :
    ((D.originalWeightedRealJacobianEquiv w a).symm z).val =
      (D.originalWeightedJacobianEquiv w a).symm (WeightedCoeffPair.complexCLM (sourceFrequencyWeight w) z) := by
  apply (D.originalWeightedJacobianEquiv w a).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change fderiv ℂ (originalWeightedBirkhoffMap hp hp1 s w) a.val _ = _
  rw [← D.originalWeightedRealMap_fderiv_complex_inclusion]
  change WeightedCoeffPair.complexCLM (sourceFrequencyWeight w)
    (D.originalWeightedRealJacobianEquiv w a ((D.originalWeightedRealJacobianEquiv w a).symm z)) = _
  rw [ContinuousLinearEquiv.apply_symm_apply]

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
