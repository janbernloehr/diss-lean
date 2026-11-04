import NLS.SequenceSpaces.NatL2HeadTailAssembly
import NLS.KdV.HillFiniteCartesianAnalyticHead
import NLS.KdV.HillUniformCriticalCartesianTails
import NLS.KdV.HillWeightedSpectralSequence

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- The existing full physical weighted Cartesian Hilbert sequence has
a complex Banach analytic extension on one native source ball near zero,
with the source radius chosen before every spectral weight. -/
theorem exists_hillWeightedSpectralSequence_common_analytic_zero_neighborhood :
    ∃ δ : ℝ, 0<δ ∧ ∀ w : SpectralWeight,
      ∃ F : WeightedCoeff w.doubleIndex.toWeight 2 → lp (fun _ : ℕ => ℂ) 2,
        AnalyticOnNhd ℂ F (ball 0 δ) ∧
        ∀ q : RealHillWeightedPotential w, ‖q.val‖<δ →
          F q.val=hillWeightedSpectralSequence h0q h0r w q := by
  obtain ⟨δt,C,N,hδt,hC,hN,htails⟩ := exists_hillNativeCriticalCartesianTails_uniform_analytic h0q h0r
  obtain ⟨δh,ε,Z,hδh,hε,hhead,hreal⟩ := exists_hillSpectralCartesian_finite_analytic_head h0q h0r 0 h0q h0r N
  simp only [map_zero] at hhead
  let δ := min δt (min δh ε)
  have hδ : 0<δ := lt_min hδt (lt_min hδh hε)
  have hdt : δ≤δt := min_le_left _ _
  have hdh : δ≤δh := (min_le_right _ _).trans (min_le_left _ _)
  have hde : δ≤ε := (min_le_right _ _).trans (min_le_right _ _)
  let K := N-1
  refine ⟨δ,hδ,?_⟩
  intro w
  obtain ⟨T,_,hTa,_,hTb,hTr⟩ := htails w N le_rfl
  let a : WeightedCoeff w.doubleIndex.toWeight 2 → ℕ → ℂ := fun q k =>
    (w (2*((k+1 : ℕ) : ℤ)) : ℂ)*(Real.sqrt (2*Real.pi*((k+1 : ℕ) : ℝ)) : ℂ)*
      Z (k+1) (hillPeriodOneCoefficientMap w q)
  let b : ℕ → ℝ := fun k =>
    ‖(w (2*((k+1 : ℕ) : ℤ)) : ℂ)*(Real.sqrt (2*Real.pi*((k+1 : ℕ) : ℝ)) : ℂ)‖*
      (‖Z (k+1) 0‖+1)
  have hidx (k : ℕ) (hk : k<K) : k+1<N := by dsimp only [K] at hk;omega
  have hparam (q : WeightedCoeff w.doubleIndex.toWeight 2) (hq : q∈ball 0 δ) :
      hillPeriodOneCoefficientMap w q∈ball 0 δh := by
    rw [mem_ball,dist_zero_right]
    exact (norm_hillPeriodOneCoefficientMap_le w q).trans_lt
      ((show ‖q‖<δ by simpa only [mem_ball,dist_zero_right] using hq).trans_le hdh)
  have ha : ∀ k<K, AnalyticOnNhd ℂ (fun q => a q k) (ball 0 δ) := by
    intro k hk q hq
    exact analyticAt_const.mul (((hhead (k+1) (hidx k hk)).1 _ (hparam q hq)).comp
      ((hillPeriodOneCoefficientMap w).analyticAt q))
  have hab (q : WeightedCoeff w.doubleIndex.toWeight 2) (hq : q∈ball 0 δ) (k : ℕ) (hk : k<K) : ‖a q k‖≤b k := by
    change ‖((w (2*((k+1 : ℕ) : ℤ)) : ℂ)*(Real.sqrt (2*Real.pi*((k+1 : ℕ) : ℝ)) : ℂ))*
      Z (k+1) (hillPeriodOneCoefficientMap w q)‖≤_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((hhead (k+1) (hidx k hk)).2 _ (hparam q hq)) (norm_nonneg _)
  obtain ⟨F,hFa,_,hcoord⟩ := Coeff.exists_natL2_analytic_head_tail (ball 0 δ) isOpen_ball K a T ha
    (hTa.mono (ball_subset_ball hdt)) b (C*(δt^2+512*δt^4)) hab
    (fun q hq => (hTb q (ball_subset_ball hdt hq)).1)
  refine ⟨F,hFa,?_⟩
  intro q hq
  have hqb : q.val∈ball 0 δ := by simpa only [mem_ball,dist_zero_right] using hq
  let r : RealPeriodOneHillPotential := hillRealWeightedEmbedding w q
  have hr : dist r (⟨0,h0q,h0r⟩ : RealPeriodOneHillPotential)<ε := by
    change dist (hillPeriodOneUnitPotential w q.val) (0 : WeightedCoeff SpectralWeight.one.toWeight 2)<ε
    rw [dist_zero_right]
    exact (norm_hillPeriodOneUnitPotential_le w q.val).trans_lt (hq.trans_le hde)
  ext k
  rw [hcoord q.val hqb k,hillWeightedSpectralSequence_apply]
  by_cases hk : k<K
  · rw [if_pos hk]
    change (w (2*((k+1 : ℕ) : ℤ)) : ℂ)*(Real.sqrt (2*Real.pi*((k+1 : ℕ) : ℝ)) : ℂ)*
      Z (k+1) (hillPeriodOneCoefficientMap w q.val)=_
    rw [hillPeriodOneCoefficientMap_eq_unit]
    have hz := hreal r hr (k+1) (hidx k hk) (by omega)
    change Z (k+1) (SpectralWeight.one.toCoeff (hillPeriodOneUnitPotential w q.val))=_ at hz
    rw [hz]
    rfl
  · rw [if_neg hk]
    have hi : k-K+N=k+1 := by dsimp only [K] at hk ⊢;omega
    have hh := (hTr q (hq.trans_le hdt) (k-K)).1
    simpa only [hi,hillWeightedSpectralCoordinate,hillRealWeightedEmbedding] using hh

end NLS.KdV
