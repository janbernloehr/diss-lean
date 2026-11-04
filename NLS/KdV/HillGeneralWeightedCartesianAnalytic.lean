import NLS.KdV.HillGeneralCartesianTails
import NLS.KdV.HillFullWeightedCartesianAnalytic
import NLS.SequenceSpaces.NatL2AnalyticGermHeadTail

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

private theorem eventually_mem_of_continuous_at
    {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (f : A → B) (x : A) (hf : ContinuousAt f x) (U : Set B) (hU : IsOpen U) (hx : f x∈U) :
    ∀ᶠ y in 𝓝 x, f y∈U := hf.preimage_mem_nhds (hU.mem_nhds hx)

private theorem eventually_dist_of_continuous_at
    {A B : Type*} [TopologicalSpace A] [PseudoMetricSpace B]
    (f : A → B) (x : A) (hf : ContinuousAt f x) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ y in 𝓝 x, dist (f y) (f x)<ε :=
  hf.tendsto.eventually (isOpen_ball.mem_nhds (mem_ball_self hε))

private theorem weighted_cartesian_tail_coordinate
    (w : SpectralWeight) (r : RealHillWeightedPotential w) (N : ℕ) (hN : 1≤N) (k : ℕ) :
    (w (2*((k+N : ℕ) : ℤ)) : ℂ)*(Real.sqrt (2*Real.pi*((k+N : ℕ) : ℝ)) : ℂ)*
      hillSpectralCartesian (hillPeriodOneUnitPotential w r.val)
        (hillPeriodOneUnitPotential_even w r.val) (hillPeriodOneUnitPotential_real w r.val r.property)
        (k+N) (by omega)=hillWeightedSpectralSequence h0q h0r w r (k+(N-1)) := by
  rw [hillWeightedSpectralSequence_apply]
  have hi : k+(N-1)+1=k+N := by omega
  simp only [hillWeightedSpectralCoordinate,hi,hillRealWeightedEmbedding]

private theorem eventual_matching_of_two_conditions
    {R I : Type*} [TopologicalSpace R] (r0 : R)
    (A B : R → Prop) (f g h : R → I → ℂ)
    (hA : ∀ᶠ r in 𝓝 r0, A r) (hB : ∀ᶠ r in 𝓝 r0, B r)
    (hfg : ∀ r, A r → B r → ∀ k, f r k=g r k)
    (hgh : ∀ r k, g r k=h r k) :
    ∀ᶠ r in 𝓝 r0, ∀ k, f r k=h r k := by
  filter_upwards [hA,hB] with r hrA hrB
  intro k
  exact (hfg r hrA hrB k).trans (hgh r k)

private theorem native_tail_eventual_matching
    (w : SpectralWeight) (q0 : RealHillWeightedPotential w) (N : ℕ) (hN : 1≤N)
    (L : ℝ) (V : Set RealPeriodOneHillPotential)
    (T : WeightedCoeff w.doubleIndex.toWeight 2 → Coeff 2)
    (hnearNorm : ∀ᶠ r : RealHillWeightedPotential w in 𝓝 q0, ‖r.val‖<L)
    (hnearV : ∀ᶠ r : RealHillWeightedPotential w in 𝓝 q0, hillRealWeightedEmbedding w r∈V)
    (hTr : ∀ r : RealHillWeightedPotential w, hillRealWeightedEmbedding w r∈V → ‖r.val‖<L → ∀ k : ℕ,
      T r.val (Equiv.intEquivNat.symm k)=
        (w (2*((k+N : ℕ) : ℤ)) : ℂ)*(Real.sqrt (2*Real.pi*((k+N : ℕ) : ℝ)) : ℂ)*
          hillSpectralCartesian (hillPeriodOneUnitPotential w r.val)
            (hillPeriodOneUnitPotential_even w r.val) (hillPeriodOneUnitPotential_real w r.val r.property)
            (k+N) (by omega)) :
    ∀ᶠ r : RealHillWeightedPotential w in 𝓝 q0, ∀ k : ℕ,
      T r.val (Equiv.intEquivNat.symm k)=hillWeightedSpectralSequence h0q h0r w r (k+(N-1)) := by
  exact eventual_matching_of_two_conditions q0
    (fun r => hillRealWeightedEmbedding w r∈V) (fun r => ‖r.val‖<L)
    (fun r k => T r.val (Equiv.intEquivNat.symm k))
    (fun r k => (w (2*((k+N : ℕ) : ℤ)) : ℂ)*(Real.sqrt (2*Real.pi*((k+N : ℕ) : ℝ)) : ℂ)*
      hillSpectralCartesian (hillPeriodOneUnitPotential w r.val)
        (hillPeriodOneUnitPotential_even w r.val) (hillPeriodOneUnitPotential_real w r.val r.property)
        (k+N) (by omega))
    (fun r k => hillWeightedSpectralSequence h0q h0r w r (k+(N-1))) hnearV hnearNorm hTr
    (fun r k => weighted_cartesian_tail_coordinate h0q h0r w r N hN k)

/-- A complex Hilbert analytic germ of the full actual weighted
Cartesian sequence at every real native source. -/
theorem exists_hillWeightedSpectralSequence_analytic_at_real_source
    (w : SpectralWeight) (q0 : RealHillWeightedPotential w) :
    ∃ F : WeightedCoeff w.doubleIndex.toWeight 2 → lp (fun _ : ℕ => ℂ) 2,
      AnalyticAt ℂ F q0.val ∧
      ∀ᶠ r : RealHillWeightedPotential w in 𝓝 q0, F r.val=hillWeightedSpectralSequence h0q h0r w r := by
  let qR := hillRealWeightedEmbedding w q0
  let p0 := SpectralWeight.one.toCoeff qR.val
  let L := ‖q0.val‖+1
  have hL : 0≤L := by dsimp only [L];positivity
  have hqL : ‖q0.val‖<L := by dsimp only [L];linarith
  obtain ⟨δt,C,N,V,hδt,hC,hN,hV,hqV,hsource,htails⟩ :=
    exists_hillNativeCriticalCartesianTails_general_analytic qR.val qR.property.1 qR.property.2 h0q h0r L hL
  obtain ⟨δh,ε,Z,hδh,hε,hhead,hreal⟩ := exists_hillSpectralCartesian_finite_analytic_head h0q h0r
    qR.val qR.property.1 qR.property.2 N
  obtain ⟨T,_,hTa,_,hTb,hTr⟩ := htails w N le_rfl
  let δ := min δt δh
  have hδ : 0<δ := lt_min hδt hδh
  have hdt : δ≤δt := min_le_left _ _
  have hdh : δ≤δh := min_le_right _ _
  let U := hillNativeSourceDomain w p0 δ L
  have hU : IsOpen U := isOpen_hillNativeSourceDomain w p0 δ L
  have hcoef0 : hillPeriodOneCoefficientMap w q0.val=p0 := hillPeriodOneCoefficientMap_eq_unit w q0.val
  have hqU : q0.val∈U := by
    refine ⟨?_,hqL⟩
    rw [hcoef0]
    exact mem_ball_self hδ
  let K := N-1
  let a : WeightedCoeff w.doubleIndex.toWeight 2 → ℕ → ℂ := fun r k =>
    (w (2*((k+1 : ℕ) : ℤ)) : ℂ)*(Real.sqrt (2*Real.pi*((k+1 : ℕ) : ℝ)) : ℂ)*
      Z (k+1) (hillPeriodOneCoefficientMap w r)
  let b : ℕ → ℝ := fun k =>
    ‖(w (2*((k+1 : ℕ) : ℤ)) : ℂ)*(Real.sqrt (2*Real.pi*((k+1 : ℕ) : ℝ)) : ℂ)‖*
      (‖Z (k+1) p0‖+1)
  have hidx (k : ℕ) (hk : k<K) : k+1<N := by dsimp only [K] at hk;omega
  have ha : ∀ k<K, AnalyticOnNhd ℂ (fun r => a r k) U := by
    dsimp only [a,U,K]
    as_aux_lemma =>
      intro k hk
      exact analyticOnNhd_const.mul (analyticOnNhd_hillNativeSource_pullback w p0 δ L (Z (k+1))
        ((hhead (k+1) (by omega)).1.mono (ball_subset_ball hdh)))
  have hab (r : WeightedCoeff w.doubleIndex.toWeight 2) (hr : r∈U) (k : ℕ) (hk : k<K) : ‖a r k‖≤b k := by
    dsimp only [a,b]
    dsimp only [U] at hr
    dsimp only [K] at hk
    as_aux_lemma =>
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left ((hhead (k+1) (by omega)).2 _ (ball_subset_ball hdh hr.1)) (norm_nonneg _)
  have hnearNorm : ∀ᶠ r : RealHillWeightedPotential w in 𝓝 q0, ‖r.val‖<L :=
    (continuous_subtype_val.continuousAt.norm).eventually (gt_mem_nhds hqL)
  have hnearV : ∀ᶠ r : RealHillWeightedPotential w in 𝓝 q0, hillRealWeightedEmbedding w r∈V :=
    eventually_mem_of_continuous_at (hillRealWeightedEmbedding w) q0
      (continuous_hillRealWeightedEmbedding w).continuousAt V hV hqV
  have hnearHead : ∀ᶠ r : RealHillWeightedPotential w in 𝓝 q0, dist (hillRealWeightedEmbedding w r) qR<ε :=
    eventually_dist_of_continuous_at (hillRealWeightedEmbedding w) q0
      (continuous_hillRealWeightedEmbedding w).continuousAt ε hε
  have hheadMatch : ∀ᶠ r : RealHillWeightedPotential w in 𝓝 q0, ∀ k<K,
      a r.val k=hillWeightedSpectralSequence h0q h0r w r k := by
    dsimp only [a,K]
    dsimp only [K] at hidx
    as_aux_lemma =>
      filter_upwards [hnearHead] with r hrH
      intro k hk
      rw [hillWeightedSpectralSequence_apply]
      rw [hillPeriodOneCoefficientMap_eq_unit]
      have hz := hreal (hillRealWeightedEmbedding w r) hrH (k+1) (hidx k hk) (by omega)
      change Z (k+1) (SpectralWeight.one.toCoeff (hillPeriodOneUnitPotential w r.val))=_ at hz
      rw [hz]
      rfl
  have htailMatch : ∀ᶠ r : RealHillWeightedPotential w in 𝓝 q0, ∀ k : ℕ,
      T r.val (Equiv.intEquivNat.symm k)=hillWeightedSpectralSequence h0q h0r w r (k+K) := by
    exact native_tail_eventual_matching h0q h0r w q0 N hN L V T hnearNorm hnearV
      (fun r hrV hrNorm k => (hTr r hrV hrNorm k).1)
  exact Coeff.exists_natL2_analytic_germ_of_head_tail_matching
    (fun r : RealHillWeightedPotential w => r.val) continuous_subtype_val q0
    (hillWeightedSpectralSequence h0q h0r w) U hU hqU K a T ha
    (hTa.mono (fun r hr => ⟨ball_subset_ball hdt hr.1,hr.2⟩)) b (C*(L^2+512*L^4)) hab
    (fun r hr => (hTb r (ball_subset_ball hdt hr.1) hr.2).1) hheadMatch htailMatch

/-- The germ extends over an open complex native neighborhood and
matches the physical Cartesian map on a real neighborhood. -/
theorem exists_hillWeightedSpectralSequence_analytic_general_neighborhood
    (w : SpectralWeight) (q0 : RealHillWeightedPotential w) :
    ∃ U : Set (WeightedCoeff w.doubleIndex.toWeight 2),
      IsOpen U ∧ q0.val∈U ∧ ∃ F : WeightedCoeff w.doubleIndex.toWeight 2 → lp (fun _ : ℕ => ℂ) 2,
        AnalyticOnNhd ℂ F U ∧
        ∀ᶠ r : RealHillWeightedPotential w in 𝓝 q0, r.val∈U ∧ F r.val=hillWeightedSpectralSequence h0q h0r w r := by
  obtain ⟨F,hF,hmatch⟩ := exists_hillWeightedSpectralSequence_analytic_at_real_source h0q h0r w q0
  let U : Set (WeightedCoeff w.doubleIndex.toWeight 2) := {x | AnalyticAt ℂ F x}
  have hU : IsOpen U := isOpen_analyticAt ℂ F
  refine ⟨U,hU,hF,F,(fun x hx => hx),?_⟩
  have hnear : ∀ᶠ r : RealHillWeightedPotential w in 𝓝 q0, r.val∈U :=
    eventually_mem_of_continuous_at (fun r : RealHillWeightedPotential w => r.val) q0
      continuous_subtype_val.continuousAt U hU hF
  exact hnear.and hmatch

end NLS.KdV
