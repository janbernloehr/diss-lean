import NLS.KdV.HillIndexedGlobalFlows
import NLS.KdV.HillDirichletSheetRoot

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Exact conservation of the actual energy discriminant on every global
indexed trajectory, without a source-mean restriction on a supplied curve. -/
theorem hillL2Discriminant_eq_on_global_indexedCurve
    (k : ℕ) (hk : 1≤k) (γ : ℝ → hillRealSourceSubmodule)
    (hγ : ∀ t : ℝ, HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t)
    (u v : ℝ) (E : ℂ) :
    hillL2Discriminant (SpectralWeight.one.toCoeff (γ u).val) E=
      hillL2Discriminant (SpectralWeight.one.toCoeff (γ v).val) E := by
  let a : ℝ := min u v-1
  let b : ℝ := max u v+1
  have hu : u∈Ioo a b := ⟨by dsimp only [a];linarith [min_le_left u v],
    by dsimp only [b];linarith [le_max_left u v]⟩
  have hv : v∈Ioo a b := ⟨by dsimp only [a];linarith [min_le_right u v],
    by dsimp only [b];linarith [le_max_right u v]⟩
  exact hillL2Discriminant_eq_on_indexed_integralCurve k hk γ a b (fun t _ => hγ t) u v hu hv E

/-- Both original periodic endpoints of every gap stay fixed on a global
indexed trajectory, including at collapsed gaps. -/
theorem hillPeriodicEndpoints_eq_on_global_indexedCurve
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k) (γ : ℝ → hillRealSourceSubmodule)
    (hγ : ∀ t : ℝ, HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t)
    (u v : ℝ) :
    hillRealLabels (γ u).val (γ u).property.1 (γ u).property.2 (2*n-1)=
      hillRealLabels (γ v).val (γ v).property.1 (γ v).property.2 (2*n-1) ∧
    hillRealLabels (γ u).val (γ u).property.1 (γ u).property.2 (2*n)=
      hillRealLabels (γ v).val (γ v).property.1 (γ v).property.2 (2*n) := by
  let a : ℝ := min u v-1
  let b : ℝ := max u v+1
  have hu : u∈Ioo a b := ⟨by dsimp only [a];linarith [min_le_left u v],
    by dsimp only [b];linarith [le_max_left u v]⟩
  have hv : v∈Ioo a b := ⟨by dsimp only [a];linarith [min_le_right u v],
    by dsimp only [b];linarith [le_max_right u v]⟩
  obtain ⟨hM,hD⟩ := hillGapGeometry_eq_on_indexed_integralCurve n k hn hk γ a b (fun t _ => hγ t) u v hu hv
  dsimp only [hillRealGapCenter,hillRealGapHalfLength] at hM hD
  constructor <;> linarith

/-- The actual selected terminal evolves on its fixed original Hill sheet:
the energy and full sheet satisfy the exact two-coordinate ODE and the
actual squared-sheet identity throughout all real time. -/
theorem hillGlobalIndexedCurve_fixed_sheet_dynamics
    (k : ℕ) (hk : 1≤k) (γ : ℝ → hillRealSourceSubmodule)
    (hγ : ∀ t : ℝ, HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t) :
    let μ : ℝ → ℂ := fun t => hillDirichletEnergy (γ t).val (γ t).property.1 (γ t).property.2 k hk
    let S : ℝ → ℂ := fun t => hillDirichletSheetRoot (SpectralWeight.one.toCoeff (γ t).val) (μ t)
    let Δ : ℂ → ℂ := hillL2Discriminant (SpectralWeight.one.toCoeff (γ 0).val)
    ∀ t : ℝ, HasDerivAt μ (S t/2) t ∧
      HasDerivAt S (Δ (μ t)*deriv Δ (μ t)/2) t ∧ S t^2=Δ (μ t)^2-4 := by
  intro μ S Δ t
  have heq : hillL2Discriminant (SpectralWeight.one.toCoeff (γ t).val)=Δ :=
    funext (fun E => hillL2Discriminant_eq_on_global_indexedCurve k hk γ hγ t 0 E)
  have hμ := hasDerivAt_hillDirichletEnergy_indexed_integralCurve k k hk hk γ t (hγ t)
  have hS := hasDerivAt_hillDirichletSheet_indexed_integralCurve k k hk hk γ t (hγ t)
  simp only [if_true] at hμ hS
  refine ⟨hμ,?_,?_⟩
  · rw [heq] at hS
    exact hS
  · have hs := hillDirichletSheetRoot_sq_of_characteristic_zero
      (SpectralWeight.one.toCoeff (γ t).val) (μ t)
      (hillDirichletEnergy_zero (γ t).val (γ t).property.1 (γ t).property.2 k hk)
    change S t^2=hillL2Discriminant (SpectralWeight.one.toCoeff (γ t).val) (μ t)^2-4 at hs
    rwa [heq] at hs

end NLS.KdV
