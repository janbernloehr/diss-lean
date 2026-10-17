import NLS.ZakharovShabat.SourceBirkhoffMapAnalytic
import NLS.ZakharovShabat.NormalizedWeightedSourceTopology

/-! # Weighted complex Birkhoff sequences in normalized coordinates

Actual weighted membership rules out the total constructor's fallback.
A common norm bound then upgrades scalar coordinate analyticity to
analyticity in the full weighted target norm.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original complex coordinates multiplied by their physical source-frequency weights. -/
def normalizedWeightedBirkhoffMap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) (w : SpectralWeight)
    (ψ : CoeffPair p) : Coeff p × Coeff p :=
  (Coeff.ofFunctionOrZero p (fun n => (w (2*n):ℂ)*(sourceBirkhoffMap hp hp1 s (normalizedWeightedSource w ψ)).1 n),
   Coeff.ofFunctionOrZero p (fun n => (w (2*n):ℂ)*(sourceBirkhoffMap hp hp1 s (normalizedWeightedSource w ψ)).2 n))

theorem normalizedWeightedBirkhoffMap_apply_of_mem
    (hp : p ≠ ⊤) (hp1 : 1 < p) (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n)
    (w : SpectralWeight) (ψ : CoeffPair p)
    (hx : Memℓp (fun n => (w (2*n):ℂ)*(sourceBirkhoffMap hp hp1 s (normalizedWeightedSource w ψ)).1 n) p)
    (hy : Memℓp (fun n => (w (2*n):ℂ)*(sourceBirkhoffMap hp hp1 s (normalizedWeightedSource w ψ)).2 n) p)
    (n : ℤ) :
    (normalizedWeightedBirkhoffMap hp hp1 s w ψ).1 n =
      (w (2*n):ℂ)*(sourceBirkhoffMap hp hp1 s (normalizedWeightedSource w ψ)).1 n ∧
    (normalizedWeightedBirkhoffMap hp hp1 s w ψ).2 n =
      (w (2*n):ℂ)*(sourceBirkhoffMap hp hp1 s (normalizedWeightedSource w ψ)).2 n :=
  ⟨Coeff.ofFunctionOrZero_apply_of_mem p _ hx n,Coeff.ofFunctionOrZero_apply_of_mem p _ hy n⟩

private theorem analytic_weighted_observation
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]
    (J : E →L[ℂ] F) (f : F → G) (L : G →L[ℂ] ℂ) (c : ℂ) (a : E)
    (hf : AnalyticAt ℂ f (J a)) : AnalyticAt ℂ (fun b => c*L (f (J b))) a := by
  have h : AnalyticAt ℂ (fun b => L (f (J b))) a :=
    (L.analyticAt _).comp (f := fun b => f (J b)) (hf.compContinuousLinearMap (u := J))
  exact analyticAt_const.mul h

namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Local bounds of actual weighted sequences give weighted Banach analyticity. -/
theorem normalizedWeightedBirkhoffMap_analytic_of_bound
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (w : SpectralWeight)
    (U : Set (CoeffPair p)) (hU : IsOpen U)
    (hUW : ∀ ψ ∈ U, normalizedWeightedSource w ψ ∈ W)
    (hmem : ∀ ψ ∈ U,
      Memℓp (fun n => (w (2*n):ℂ)*(sourceBirkhoffMap hp hp1 s (normalizedWeightedSource w ψ)).1 n) p ∧
      Memℓp (fun n => (w (2*n):ℂ)*(sourceBirkhoffMap hp hp1 s (normalizedWeightedSource w ψ)).2 n) p)
    (M : ℝ) (hbound : ∀ ψ ∈ U, ‖normalizedWeightedBirkhoffMap hp hp1 s w ψ‖ ≤ M) :
    AnalyticOnNhd ℂ (normalizedWeightedBirkhoffMap hp hp1 s w) U := by
  have he ψ (hψ : ψ ∈ U) := normalizedWeightedBirkhoffMap_apply_of_mem hp hp1 s w ψ (hmem ψ hψ).1 (hmem ψ hψ).2
  have hx : AnalyticOnNhd ℂ (fun ψ => (normalizedWeightedBirkhoffMap hp hp1 s w ψ).1) U := by
    apply Coeff.analyticOnNhd_of_bounded_coordinatewise _ hU _ M
      (fun ψ hψ => (norm_fst_le _).trans (hbound ψ hψ))
    intro n ψ hψ
    let L := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp (ContinuousLinearMap.fst ℂ (Coeff p) (Coeff p))
    apply (analytic_weighted_observation (normalizedWeightedSourceCLM w) (sourceBirkhoffMap hp hp1 s)
      L (w (2*n)) ψ (D.analytic _ (hUW ψ hψ))).congr
    filter_upwards [hU.mem_nhds hψ] with χ hχ
    exact (he χ hχ n).1.symm
  have hy : AnalyticOnNhd ℂ (fun ψ => (normalizedWeightedBirkhoffMap hp hp1 s w ψ).2) U := by
    apply Coeff.analyticOnNhd_of_bounded_coordinatewise _ hU _ M
      (fun ψ hψ => (norm_snd_le _).trans (hbound ψ hψ))
    intro n ψ hψ
    let L := (lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).comp (ContinuousLinearMap.snd ℂ (Coeff p) (Coeff p))
    apply (analytic_weighted_observation (normalizedWeightedSourceCLM w) (sourceBirkhoffMap hp hp1 s)
      L (w (2*n)) ψ (D.analytic _ (hUW ψ hψ))).congr
    filter_upwards [hU.mem_nhds hψ] with χ hχ
    exact (he χ hχ n).2.symm
  exact fun ψ hψ => (hx ψ hψ).prod (hy ψ hψ)

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
