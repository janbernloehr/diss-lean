import NLS.ZakharovShabat.SourceBirkhoffWeightedCanonical

/-! # Scalar analytic extensions on a common weighted source domain

The common domain is the preimage of the unweighted analytic domain.
Each scalar extension agrees with its original weighted real coordinate.
This does not assert weighted sequence-valued analyticity.
-/
noncomputable section
open Set NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem open_preimage_linear {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (J : E →L[ℂ] F) (U : Set F) (hU : IsOpen U) : IsOpen (J ⁻¹' U) :=
  hU.preimage J.continuous

private theorem analytic_scalar_pullback {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (J : E →L[ℂ] F) (f : F → G) (L : G →L[ℂ] ℂ) (a : E)
    (hf : AnalyticAt ℂ f (J a)) : AnalyticAt ℂ (fun b => L (f (J b))) a :=
  (L.analyticAt _).comp (hf.compContinuousLinearMap (u := J))

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- One common open weighted domain contains the entire weighted real subspace. -/
theorem originalWeightedBirkhoff_domain
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight) :
    IsOpen (originalWeightedSourceCLM (p := p) w ⁻¹' W) ∧
      ∀ a : weightedRealSourceSubmodule (p := p) w, originalWeightedSourceCLM (p := p) w a.val ∈ W := by
  constructor
  · exact open_preimage_linear (originalWeightedSourceCLM (p := p) w) W D.source_open
  · intro a
    rw [originalWeightedSourceCLM_real]
    exact D.real_subset (originalWeightedRealSource w a).property

/-- Each actual original coordinate has a complex power-series extension
at every point of the common weighted domain. -/
theorem originalWeightedBirkhoff_analytic
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (a : WeightedCoeffPair (sourceFrequencyWeight w) p)
    (ha : originalWeightedSourceCLM w a ∈ W) (n : ℤ) :
    AnalyticAt ℂ (originalWeightedBirkhoffX hp hp1 s w n) a ∧
      AnalyticAt ℂ (originalWeightedBirkhoffY hp hp1 s w n) a := by
  let ex := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p))
  let ey := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p))
  exact ⟨analytic_scalar_pullback (originalWeightedSourceCLM (p := p) w)
      (sourceBirkhoffMap hp hp1 s) ex a (D.analytic _ ha),
    analytic_scalar_pullback (originalWeightedSourceCLM (p := p) w)
      (sourceBirkhoffMap hp hp1 s) ey a (D.analytic _ ha)⟩

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
