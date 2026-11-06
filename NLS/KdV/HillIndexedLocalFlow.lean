import NLS.KdV.HillRealIndexedField
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Picard-Lindelof constructs a local flow of the genuine indexed Hill field
on the actual complete real source space. -/
theorem exists_hillRealIndexedDiscriminant_localFlow
    (n : ℕ) (hn : 1≤n) (q : hillRealSourceSubmodule) :
    ∃ α : hillRealSourceSubmodule → ℝ → hillRealSourceSubmodule,
      ∀ᶠ xt in 𝓝 q ×ˢ 𝓝 (0 : ℝ),
        α xt.1 0=xt.1 ∧ HasDerivAt (α xt.1) (hillRealIndexedDiscriminantField n hn (α xt.1 xt.2)) xt.2 :=
  (contDiff_hillRealIndexedDiscriminantField n hn).contDiffAt.exists_eventually_eq_hasDerivAt 0

/-- Every actual indexed Hill integral curve conserves the entire discriminant
throughout its open interval of definition. -/
theorem hillL2Discriminant_eq_on_indexed_integralCurve
    (n : ℕ) (hn : 1≤n) (γ : ℝ → hillRealSourceSubmodule) (a b : ℝ)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (hillRealIndexedDiscriminantField n hn (γ t)) t)
    (u v : ℝ) (hu : u∈Ioo a b) (hv : v∈Ioo a b) (E : ℂ) :
    hillL2Discriminant (SpectralWeight.one.toCoeff (γ u).val) E=
      hillL2Discriminant (SpectralWeight.one.toCoeff (γ v).val) E := by
  let P : hillRealSourceSubmodule →L[ℝ] Coeff 2 :=
    (SpectralWeight.one.toCoeff.restrictScalars ℝ).comp hillRealSourceSubmodule.subtypeL
  have hd (t : ℝ) (ht : t∈Ioo a b) :
      HasDerivAt (fun τ => hillL2Discriminant (SpectralWeight.one.toCoeff (γ τ).val) E) 0 t := by
    have hD : DifferentiableAt ℂ (fun p : Coeff 2 => hillL2Discriminant p E)
        (SpectralWeight.one.toCoeff (γ t).val) :=
      ((analyticOnNhd_hillL2Discriminant_joint (E,SpectralWeight.one.toCoeff (γ t).val) (mem_univ _)).comp
        (f := fun p : Coeff 2 => (E,p)) (analyticAt_const.prod analyticAt_id)).differentiableAt
    have hc := (hD.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t
      (P.hasFDerivAt.comp_hasDerivAt t (hγ t ht))
    change HasDerivAt (fun τ => hillL2Discriminant (SpectralWeight.one.toCoeff (γ τ).val) E)
      ((fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E) (SpectralWeight.one.toCoeff (γ t).val))
        (SpectralWeight.one.toCoeff (hillIndexedDiscriminantHamiltonianSource ⟨(γ t).val,(γ t).property.1,(γ t).property.2⟩ n hn))) t at hc
    have hz := hillIndexedDiscriminantHamiltonianSource_isospectral
      (⟨(γ t).val,(γ t).property.1,(γ t).property.2⟩ : RealPeriodOneHillPotential) n hn E
    exact hz ▸ hc
  exact isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) hu hv

/-- Every genuine indexed Hill integral curve also conserves its actual mean. -/
theorem hillMean_eq_on_indexed_integralCurve
    (n : ℕ) (hn : 1≤n) (γ : ℝ → hillRealSourceSubmodule) (a b : ℝ)
    (hγ : ∀ t ∈ Ioo a b, HasDerivAt γ (hillRealIndexedDiscriminantField n hn (γ t)) t)
    (u v : ℝ) (hu : u∈Ioo a b) (hv : v∈Ioo a b) :
    (γ u).val.val 0=(γ v).val.val 0 := by
  let M : hillRealSourceSubmodule →L[ℝ] ℂ :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).restrictScalars ℝ).comp
      ((SpectralWeight.one.toCoeff.restrictScalars ℝ).comp hillRealSourceSubmodule.subtypeL)
  have hd (t : ℝ) (ht : t∈Ioo a b) : HasDerivAt (fun τ => M (γ τ)) 0 t := by
    have hc := M.hasFDerivAt.comp_hasDerivAt t (hγ t ht)
    have hz : M (hillRealIndexedDiscriminantField n hn (γ t))=0 := by
      change (SpectralWeight.one.toCoeff (hillIndexedDiscriminantHamiltonianSource
        ⟨(γ t).val,(γ t).property.1,(γ t).property.2⟩ n hn)) 0=0
      rw [SpectralWeight.toCoeff_apply]
      exact hillEnergyHamiltonianSource_mean_zero _ _
    rw [hz] at hc
    exact hc
  have he := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hd t ht).deriv) hu hv
  change (SpectralWeight.one.toCoeff (γ u).val) 0=(SpectralWeight.one.toCoeff (γ v).val) 0 at he
  simpa only [SpectralWeight.toCoeff_apply] using he

/-- Through every rough real period-one Hill source there is an actual real
indexed spectral trajectory, preserving its mean and every discriminant value. -/
theorem exists_hillIndexedDiscriminant_isospectral_integralCurve
    (n : ℕ) (hn : 1≤n) (q : RealPeriodOneHillPotential) :
    ∃ γ : ℝ → hillRealSourceSubmodule, (γ 0).val=q.val ∧
      ∃ ε : ℝ, 0<ε ∧
        (∀ t∈Ioo (-ε) ε, HasDerivAt γ (hillRealIndexedDiscriminantField n hn (γ t)) t) ∧
        (∀ t∈Ioo (-ε) ε, (γ t).val.val 0=q.val.val 0) ∧
        ∀ t∈Ioo (-ε) ε, ∀ E : ℂ,
          hillL2Discriminant (SpectralWeight.one.toCoeff (γ t).val) E=
            hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E := by
  let q₀ : hillRealSourceSubmodule := ⟨q.val,q.property⟩
  have hC := (contDiff_hillRealIndexedDiscriminantField n hn).contDiffAt (x := q₀)
  obtain ⟨γ,hγ,ε,hε,hder⟩ := hC.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0
  have hd (t : ℝ) (ht : t∈Ioo (-ε) ε) :
      HasDerivAt γ (hillRealIndexedDiscriminantField n hn (γ t)) t :=
    hder t (by simpa only [zero_sub,zero_add] using ht)
  have h0 : (0 : ℝ)∈Ioo (-ε) ε := ⟨by linarith,hε⟩
  refine ⟨γ,congrArg Subtype.val hγ,ε,hε,hd,?_,?_⟩
  · intro t ht
    simpa only [hγ] using hillMean_eq_on_indexed_integralCurve n hn γ (-ε) ε hd t 0 ht h0
  · intro t ht E
    simpa only [hγ] using hillL2Discriminant_eq_on_indexed_integralCurve n hn γ (-ε) ε hd t 0 ht h0 E

end NLS.KdV
