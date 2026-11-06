import NLS.KdV.HillOriginalQuadraticTrace
import NLS.KdV.HillIndexedFlowCartesianDynamics
import NLS.KdV.HillIndexedLocalFlow

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.LinearVolterra NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- Every actual mean-zero indexed Hill curve conserves its original rough
source norm throughout its entire interval of definition. -/
theorem hillSource_norm_eq_on_indexed_integralCurve
    (k : ℕ) (hk : 1≤k) (γ : ℝ → hillRealSourceSubmodule) (a b : ℝ)
    (hγ : ∀ t∈Ioo a b, HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t)
    (u v : ℝ) (hu : u∈Ioo a b) (hv : v∈Ioo a b) (hmean : (γ u).val.val 0=0) :
    ‖(γ u).val‖=‖(γ v).val‖ := by
  have hm : (γ v).val.val 0=0 :=
    (hillMean_eq_on_indexed_integralCurve k hk γ a b hγ v u hv hu).trans hmean
  apply hillSource_norm_eq_of_actions_eq
    (⟨(γ u).val,(γ u).property⟩ : RealPeriodOneHillPotential)
    (⟨(γ v).val,(γ v).property⟩ : RealPeriodOneHillPotential) hmean hm
  intro n hn
  exact hillRealGapIntegral_eq_on_indexed_integralCurve n k hn hk 0 γ a b hγ u v hu hv

/-- Through every original mean-zero rough Hill source there is a genuine
local indexed trajectory conserving its original norm, mean and every
energy discriminant. -/
theorem exists_hillIndexedDiscriminant_norm_preserving_integralCurve
    (k : ℕ) (hk : 1≤k) (q : RealPeriodOneHillPotential) (hmean : q.val.val 0=0) :
    ∃ γ : ℝ → hillRealSourceSubmodule, (γ 0).val=q.val ∧
      ∃ ε : ℝ, 0<ε ∧
        (∀ t∈Ioo (-ε) ε, HasDerivAt γ (hillRealIndexedDiscriminantField k hk (γ t)) t) ∧
        (∀ t∈Ioo (-ε) ε, (γ t).val.val 0=0 ∧ ‖(γ t).val‖=‖q.val‖) ∧
        ∀ t∈Ioo (-ε) ε, ∀ E : ℂ,
          hillL2Discriminant (SpectralWeight.one.toCoeff (γ t).val) E=
            hillL2Discriminant (SpectralWeight.one.toCoeff q.val) E := by
  obtain ⟨γ,hγ0,ε,hε,hD,hM,hdisc⟩ := exists_hillIndexedDiscriminant_isospectral_integralCurve k hk q
  have h0 : (0 : ℝ)∈Ioo (-ε) ε := ⟨by linarith,hε⟩
  have hm0 : (γ 0).val.val 0=0 := by rw [hγ0];exact hmean
  refine ⟨γ,hγ0,ε,hε,hD,?_,hdisc⟩
  intro t ht
  refine ⟨(hM t ht).trans hmean,?_⟩
  exact (hillSource_norm_eq_on_indexed_integralCurve k hk γ (-ε) ε hD 0 t h0 ht hm0).symm.trans
    (congrArg norm hγ0)

end NLS.KdV
