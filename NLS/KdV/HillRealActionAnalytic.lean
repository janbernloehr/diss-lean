import NLS.KdV.HillComplexWeightedEmbedding
import NLS.KdV.HillActionGapRatioAllBase
import NLS.KdV.HillWeightedActionContinuity

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



theorem exists_hillRealGapIntegral_analytic_extension
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n) :
    ∃ F : Coeff 2 → ℂ, AnalyticAt ℂ F (SpectralWeight.one.toCoeff q) ∧
      ∀ᶠ r : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
        F (SpectralWeight.one.toCoeff r.val)=(hillRealGapIntegral r.val r.property.1 r.property.2 n 0:ℂ) := by
  obtain ⟨U,_,hqU,hM,hS,_⟩ := exists_hillLocalGapSymmetricData_analytic_neighborhood q hq hr n hn
  let F : Coeff 2 → ℂ := fun p => hillLocalActionGapRatio q hq hr n p*(hillLocalGapSquare q hq hr n p/4)
  have hF : AnalyticAt ℂ F (SpectralWeight.one.toCoeff q) :=
    (analyticAt_hillLocalActionGapRatio q hq hr n hn).mul ((hS _ hqU).div_const)
  obtain ⟨V,hV,hqV,hdata⟩ := exists_hillLocalGapSymmetricData_physical_neighborhood q hq hr n hn
  refine ⟨F,hF,?_⟩
  filter_upwards [hillLocalActionGapRatio_eventually_eq_physical q hq hr n hn,hV.mem_nhds hqV] with r hratio hrV
  dsimp only [F]
  rw [hratio,(hdata r hrV).2,hillRealGapIntegral_eq_halfLength_sq_mul_ratio r.val r.property.1 r.property.2 n hn]
  ring

theorem exists_hillWeightedActionTerm_analytic_extension (w : SpectralWeight)
    (q : RealHillWeightedPotential w) (n : ℕ) :
    ∃ F : WeightedCoeff w.doubleIndex.toWeight 2 → ℂ, AnalyticAt ℂ F q.val ∧
      ∀ᶠ r : RealHillWeightedPotential w in 𝓝 q, F r.val=(hillWeightedActionTerm w r n:ℂ) := by
  by_cases hn : n=0
  · subst n
    refine ⟨fun _ => 0,analyticAt_const,Filter.Eventually.of_forall (fun r => ?_)⟩
    simp only [hillWeightedActionTerm,Nat.cast_zero,mul_zero,zero_mul,ofReal_zero]
  · have hn1 : 1≤n := by omega
    obtain ⟨G,hG,hmatch⟩ := exists_hillRealGapIntegral_analytic_extension
      (hillRealWeightedEmbedding w q).val (hillRealWeightedEmbedding w q).property.1
      (hillRealWeightedEmbedding w q).property.2 n hn1
    let A := (w (2*(n:ℤ)))^2*(2*Real.pi*(n:ℝ))
    let F : WeightedCoeff w.doubleIndex.toWeight 2 → ℂ := fun p => (A:ℂ)*G (hillPeriodOneCoefficientMap w p)
    have hGb : AnalyticAt ℂ G (hillPeriodOneCoefficientMap w q.val) := by
      rw [hillPeriodOneCoefficientMap_eq_unit]
      exact hG
    have hcomp : AnalyticAt ℂ (fun p => G (hillPeriodOneCoefficientMap w p)) q.val :=
      hGb.comp (f := hillPeriodOneCoefficientMap w) ((hillPeriodOneCoefficientMap w).analyticAt q.val)
    refine ⟨F,analyticAt_const.mul hcomp,?_⟩
    have he := (continuous_hillRealWeightedEmbedding w).tendsto q |>.eventually hmatch
    filter_upwards [he] with r hr
    dsimp only [F]
    dsimp only [hillRealWeightedEmbedding] at hr
    rw [hillPeriodOneCoefficientMap_eq_unit,hr]
    simp only [hillWeightedActionTerm,hillPeriodOneAction,A,ofReal_mul]

end NLS.KdV
