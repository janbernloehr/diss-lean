import NLS.ZakharovShabat.SourceBirkhoffWeightedRealJacobian
import Mathlib.Topology.IsLocalHomeomorph

/-! # Real analytic inverses in the native weighted spaces

The actual weighted real map has a two-sided analytic local inverse at every
real source, for every spectral weight and finite p>1. Complex inverse germs
preserve the real form locally, and the real map is an open embedding.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal ComplexConjugate
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Construct both real analytic inverse germs and the strict inverse Jacobian. -/
theorem exists_originalWeighted_real_localInverse
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w) :
    ∃ g : WithLp p (WeightedRealCoeff (sourceFrequencyWeight w) p × WeightedRealCoeff (sourceFrequencyWeight w) p) →
        weightedRealSourceSubmodule (p := p) w,
      AnalyticAt ℝ g (D.originalWeightedRealMap w a) ∧
      g (D.originalWeightedRealMap w a) = a ∧
      (∀ᶠ b in 𝓝 a, g (D.originalWeightedRealMap w b) = b) ∧
      (∀ᶠ z in 𝓝 (D.originalWeightedRealMap w a), D.originalWeightedRealMap w (g z) = z) ∧
      HasStrictFDerivAt g (D.originalWeightedRealJacobianEquiv w a).symm.toContinuousLinearMap
        (D.originalWeightedRealMap w a) := by
  have ha := D.originalWeightedRealMap_analytic w a (mem_univ a)
  have hd : HasStrictFDerivAt (D.originalWeightedRealMap w)
      (D.originalWeightedRealJacobianEquiv w a).toContinuousLinearMap a :=
    ha.contDiffAt.hasStrictFDerivAt (n := 1) one_ne_zero
  let e := hd.toOpenPartialHomeomorph (D.originalWeightedRealMap w)
  have he : (e : weightedRealSourceSubmodule (p := p) w →
      WithLp p (WeightedRealCoeff (sourceFrequencyWeight w) p × WeightedRealCoeff (sourceFrequencyWeight w) p)) =
        D.originalWeightedRealMap w := hd.toOpenPartialHomeomorph_coe
  have hg : AnalyticAt ℝ e.symm (D.originalWeightedRealMap w a) := by
    have h := e.analyticAt_symm' hd.mem_toOpenPartialHomeomorph_source
      (by rw [he]; exact ha) (i := D.originalWeightedRealJacobianEquiv w a) (by rw [he]; rfl)
    rw [he] at h
    exact h
  exact ⟨hd.localInverse _ _ _,hg,hd.localInverse_apply_image,
    hd.eventually_left_inverse,hd.eventually_right_inverse,hd.to_localInverse⟩

private theorem inverse_germ_preserves_subspace
    {E F R S : Type*} [TopologicalSpace E] [TopologicalSpace R] [TopologicalSpace S]
    (J : R → E) (hJ : Continuous J) (K : S → F) (f : E → F) (fR : R → S)
    (a : R) (g : F → E) (gR : S → R)
    (hc : ContinuousAt gR (fR a)) (hbase : gR (fR a) = a)
    (hl : ∀ᶠ b in 𝓝 (J a), g (f b) = b)
    (hr : ∀ᶠ z in 𝓝 (fR a), fR (gR z) = z)
    (hcomp : ∀ b, K (fR b) = f (J b))
    (P : E → Prop) (hP : ∀ b, P (J b)) :
    ∀ᶠ z in 𝓝 (fR a), P (g (K z)) := by
  have ht : Tendsto (fun z => J (gR z)) (𝓝 (fR a)) (𝓝 (J a)) := by
    have h := hJ.continuousAt.tendsto.comp hc.tendsto
    simpa only [Function.comp_def,hbase] using h
  filter_upwards [ht.eventually hl,hr] with z hz hzr
  have he := hcomp (gR z)
  rw [hzr] at he
  rw [he,hz]
  exact hP (gR z)

/-- Every complex left inverse germ maps nearby real targets to weighted real sources. -/
theorem originalWeighted_complex_localInverse_real_germ
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : weightedRealSourceSubmodule (p := p) w)
    (g : WeightedCoeffPair (sourceFrequencyWeight w) p → WeightedCoeffPair (sourceFrequencyWeight w) p)
    (hl : ∀ᶠ b in 𝓝 a.val, g (originalWeightedBirkhoffMap hp hp1 s w b) = b) :
    ∀ᶠ z in 𝓝 (D.originalWeightedRealMap w a),
      g (WeightedCoeffPair.complexCLM (sourceFrequencyWeight w) z) ∈ weightedRealSourceSubmodule w := by
  obtain ⟨gR,ha,hbase,_,hr,_⟩ := D.exists_originalWeighted_real_localInverse w a
  exact inverse_germ_preserves_subspace (fun b : weightedRealSourceSubmodule (p := p) w => b.val)
    continuous_subtype_val (WeightedCoeffPair.complexCLM (sourceFrequencyWeight w))
    (originalWeightedBirkhoffMap hp hp1 s w) (D.originalWeightedRealMap w) a g gR
    ha.continuousAt hbase hl hr (D.originalWeightedRealMap_complex_inclusion w)
    (fun b => b ∈ weightedRealSourceSubmodule w) (fun b => b.property)

/-- The native weighted real map is a local homeomorphism for every spectral weight. -/
theorem originalWeightedRealMap_isLocalHomeomorph
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight) :
    IsLocalHomeomorph (D.originalWeightedRealMap w) := by
  intro a
  have ha := D.originalWeightedRealMap_analytic w a (mem_univ a)
  have hd : HasStrictFDerivAt (D.originalWeightedRealMap w)
      (D.originalWeightedRealJacobianEquiv w a).toContinuousLinearMap a :=
    ha.contDiffAt.hasStrictFDerivAt (n := 1) one_ne_zero
  exact ⟨hd.toOpenPartialHomeomorph (D.originalWeightedRealMap w),
    hd.mem_toOpenPartialHomeomorph_source,hd.toOpenPartialHomeomorph_coe.symm⟩

/-- The actual weighted real map identifies its source with an open subset of its target. -/
theorem originalWeightedRealMap_isOpenEmbedding
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight) :
    IsOpenEmbedding (D.originalWeightedRealMap w) :=
  (D.originalWeightedRealMap_isLocalHomeomorph w).isOpenEmbedding_of_injective (D.originalWeightedRealMap_injective w)

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
