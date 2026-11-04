import NLS.KdV.HillUniformKernelCorrectionTerms
import NLS.KdV.HillLocallyUniformActionTails
import NLS.ComplexAnalysis.NormalAnalyticSeries

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



/-- The original regular phase restricted to high off-diagonal gaps. -/
def hillHighOffDiagonalRegularCorrection
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 1≤N) (n : ℕ) (hn : 1≤n) : ℂ :=
  ∑' k : ℕ, if hk : N≤k ∧ k≠n then
    hillRegularAbelianCorrection q hq hr n hn k (hN.trans hk.1) else 0

variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

include h0q h0r in
/-- The actual high off-diagonal phase sums are analytic and uniformly
bounded on one common native weighted source ball. Their phase multipliers
have a common exponential norm bound, before n and the spectral weight. -/
theorem exists_hillHighOffDiagonalRegularCorrection_uniform_native_analytic :
    ∃ δ M : ℝ, ∃ N : ℕ, 0<δ ∧ 0<M ∧ ∃ hN : 1≤N,
      ∀ n : ℕ, ∀ hn : 1≤n, ∀ w : SpectralWeight,
      ∃ F : WeightedCoeff w.doubleIndex.toWeight 2 → ℂ,
        AnalyticOnNhd ℂ F (ball 0 δ) ∧
        (∀ q∈ball 0 δ, ‖F q‖≤M*(∑' m : ℤ, hillOffDiagonalPeriodKernel n m)) ∧
        (∀ q : RealHillWeightedPotential w, ‖q.val‖<δ →
          F q.val=hillHighOffDiagonalRegularCorrection (hillPeriodOneUnitPotential w q.val)
            (hillPeriodOneUnitPotential_even w q.val) (hillPeriodOneUnitPotential_real w q.val q.property)
            N hN n hn) ∧
        AnalyticOnNhd ℂ (fun q => Complex.exp (I*F q)) (ball 0 δ) ∧
        ∀ q∈ball 0 δ, ‖Complex.exp (I*F q)‖≤Real.exp (4*M/Real.pi^2) := by
  obtain ⟨δ,M,N,hδ,hM,hN,hcharts⟩ := exists_hillRegularAbelianCorrection_uniform_native_kernel_charts h0q h0r
  refine ⟨δ,M,N,hδ,hM,hN,?_⟩
  intro n hn w
  obtain ⟨β,hβa,hβzero,hβbound,hphysical⟩ := hcharts n hn
  let f : ℕ → WeightedCoeff w.doubleIndex.toWeight 2 → ℂ := fun k q =>
    β k (hillPeriodOneCoefficientMap w q)
  let b : ℕ → ℝ := fun k => M*hillOffDiagonalPeriodKernel n (k : ℤ)
  have hknat : Summable (fun k : ℕ => hillOffDiagonalPeriodKernel n (k : ℤ)) :=
    (summable_hillOffDiagonalPeriodKernel n).comp_injective Int.ofNat_injective
  have hb : Summable b := hknat.mul_left M
  have hbound (k : ℕ) (q : WeightedCoeff w.doubleIndex.toWeight 2) (hq : q∈ball 0 δ) : ‖f k q‖≤b k :=
    hβbound w q (by simpa only [mem_ball,dist_zero_right] using hq) k
  have hfa (k : ℕ) : AnalyticOnNhd ℂ (f k) (ball 0 δ) := by
    intro q hq
    have hp : hillPeriodOneCoefficientMap w q∈ball 0 δ := by
      rw [mem_ball,dist_zero_right]
      exact (norm_hillPeriodOneCoefficientMap_le w q).trans_lt
        (show ‖q‖<δ by simpa only [mem_ball,dist_zero_right] using hq)
    exact (hβa k _ hp).comp ((hillPeriodOneCoefficientMap w).analyticAt q)
  let F : WeightedCoeff w.doubleIndex.toWeight 2 → ℂ := fun q => ∑' k : ℕ, f k q
  have hFa : AnalyticOnNhd ℂ F (ball 0 δ) :=
    analyticOnNhd_tsum_of_summable_uniform_bound f (ball 0 δ) isOpen_ball hfa b hb hbound
  have hsum : (∑' k : ℕ, hillOffDiagonalPeriodKernel n (k : ℤ))≤
      ∑' m : ℤ, hillOffDiagonalPeriodKernel n m := by
    exact tsum_comp_le_tsum_of_inj (summable_hillOffDiagonalPeriodKernel n)
      (hillOffDiagonalPeriodKernel_nonneg n) Int.ofNat_injective
  have hFb (q : WeightedCoeff w.doubleIndex.toWeight 2) (hq : q∈ball 0 δ) :
      ‖F q‖≤M*(∑' m : ℤ, hillOffDiagonalPeriodKernel n m) := by
    have hs : Summable (fun k : ℕ => ‖f k q‖) :=
      hb.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => hbound k q hq)
    apply (norm_tsum_le_tsum_norm hs).trans
    have hh := hs.tsum_le_tsum (fun k => hbound k q hq) hb
    change (∑' k : ℕ, ‖f k q‖)≤_ at hh
    rw [show (∑' k : ℕ, b k)=M*(∑' k : ℕ, hillOffDiagonalPeriodKernel n (k : ℤ)) from
      tsum_mul_left] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hsum hM.le)
  refine ⟨F,hFa,hFb,?_,?_,?_⟩
  · intro q hq
    let r : RealPeriodOneHillPotential := ⟨hillPeriodOneUnitPotential w q.val,
      hillPeriodOneUnitPotential_even w q.val,hillPeriodOneUnitPotential_real w q.val q.property⟩
    have hr : ‖r.val‖<δ := (norm_hillPeriodOneUnitPotential_le w q.val).trans_lt hq
    change (∑' k : ℕ, β k (hillPeriodOneCoefficientMap w q.val))=_
    unfold hillHighOffDiagonalRegularCorrection
    apply tsum_congr
    intro k
    by_cases hk : N≤k ∧ k≠n
    · rw [dif_pos hk,hillPeriodOneCoefficientMap_eq_unit]
      exact hphysical r hr k hk.1 hk.2
    · rw [dif_neg hk]
      exact congrFun (hβzero k hk) _
  · intro q hq
    exact (analyticAt_const.mul (hFa q hq)).cexp'
  · intro q hq
    have hh : ‖F q‖≤4*M/Real.pi^2 :=
      (hFb q hq).trans ((mul_le_mul_of_nonneg_left (tsum_hillOffDiagonalPeriodKernel_le n) hM.le).trans_eq (by ring))
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    apply (Complex.re_le_norm (I*F q)).trans
    simpa only [norm_mul,norm_I,one_mul] using hh

end NLS.KdV
