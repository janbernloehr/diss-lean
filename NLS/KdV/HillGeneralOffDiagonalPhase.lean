import NLS.KdV.HillNativeKernelSeries
import NLS.KdV.HillGeneralKernelCorrections

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The native kernel series agrees with the original high-gap sum
when every active term matches and every inactive term vanishes. -/
theorem hillNativeKernelSeries_eq_physical_high_sum
    (w : SpectralWeight) (β : ℕ → Coeff 2 → ℂ) (N n : ℕ) (hN : 1≤N) (hn : 1≤n)
    (r : RealHillWeightedPotential w)
    (hzero : ∀ k : ℕ, ¬(N≤k ∧ k≠n) → β k=0)
    (hreal : ∀ k : ℕ, ∀ hk : N≤k, k≠n →
      β k (SpectralWeight.one.toCoeff (hillRealWeightedEmbedding w r).val)=
        hillRegularAbelianCorrection (hillRealWeightedEmbedding w r).val
          (hillRealWeightedEmbedding w r).property.1 (hillRealWeightedEmbedding w r).property.2 n hn k (hN.trans hk)) :
    hillNativeKernelSeries w β r.val=hillHighOffDiagonalRegularCorrection
      (hillRealWeightedEmbedding w r).val (hillRealWeightedEmbedding w r).property.1
      (hillRealWeightedEmbedding w r).property.2 N hN n hn := by
  rw [hillNativeKernelSeries_apply]
  unfold hillHighOffDiagonalRegularCorrection
  apply tsum_congr
  intro k
  by_cases hk : N≤k ∧ k≠n
  · rw [dif_pos hk]
    rw [hillPeriodOneCoefficientMap_eq_unit]
    exact hreal k hk.1 hk.2
  · rw [dif_neg hk]
    exact congrFun (hzero k hk) _

variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- A normally convergent off-diagonal high phase on common bounded
native source domains around any original real source. -/
theorem exists_hillHighOffDiagonalRegularCorrection_general_native_charts (L : ℝ) (hL : 0≤L) :
    ∃ δ M : ℝ, ∃ N : ℕ, ∃ V : Set RealPeriodOneHillPotential,
      0<δ ∧ 0<M ∧ ∃ hN : 1≤N, IsOpen V ∧ (⟨q,hq,hr⟩ : RealPeriodOneHillPotential)∈V ∧
      (∀ p∈V, SpectralWeight.one.toCoeff p.val∈ball (SpectralWeight.one.toCoeff q) δ) ∧
      ∀ n : ℕ, ∀ hn : 1≤n, ∀ w : SpectralWeight,
      ∃ H : WeightedCoeff w.doubleIndex.toWeight 2 → ℂ,
        AnalyticOnNhd ℂ H (hillNativeSourceDomain w (SpectralWeight.one.toCoeff q) δ L) ∧
        (∀ r : WeightedCoeff w.doubleIndex.toWeight 2,
          hillPeriodOneCoefficientMap w r∈ball (SpectralWeight.one.toCoeff q) δ → ‖r‖<L → ‖H r‖≤M) ∧
        ∀ r : RealHillWeightedPotential w, hillRealWeightedEmbedding w r∈V → ‖r.val‖<L →
          H r.val=hillHighOffDiagonalRegularCorrection (hillPeriodOneUnitPotential w r.val)
            (hillPeriodOneUnitPotential_even w r.val) (hillPeriodOneUnitPotential_real w r.val r.property) N hN n hn := by
  obtain ⟨δ,Mh,N,V,hδ,hMh,hN,hV,hqV,hsource,hhigh⟩ :=
    exists_hillRegularAbelianCorrection_general_native_kernel_charts q hq hr h0q h0r L hL
  refine ⟨δ,4*Mh/Real.pi^2,N,V,hδ,by positivity,hN,hV,hqV,hsource,?_⟩
  intro n hn1 w
  obtain ⟨β,hβa,hβzero,hβb,hβreal⟩ := hhigh n hn1
  have hApp := hillNativeKernelSeries_analytic_bound (SpectralWeight.one.toCoeff q) w β δ L Mh n hMh.le hβa (hβb w)
  refine ⟨hillNativeKernelSeries w β,hApp.1,hApp.2,?_⟩
  intro r hrV _
  exact hillNativeKernelSeries_eq_physical_high_sum w β N n hN hn1 r hβzero
    (fun k hk hkn => hβreal (hillRealWeightedEmbedding w r) hrV k hk hkn)

end NLS.KdV
