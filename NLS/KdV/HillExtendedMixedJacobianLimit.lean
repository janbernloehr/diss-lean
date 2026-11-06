import NLS.KdV.HillMixedPeriodRowLimit
import NLS.KdV.HillMixedUniformDerivativeTail
import NLS.KdV.HillFullMixedPeriodCompact
import NLS.SequenceSpaces.FiniteRowOperatorConvergence

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- Extend the actual deleted mixed Jacobian to a common ambient Hilbert
space, inserting minus the identity at its omitted positive coordinate. -/
def hillExtendedMixedPeriodJacobian (N n : ℕ) (a p : Coeff 2) : Coeff 2 →L[ℂ] Coeff 2 :=
  fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a+
    Coeff.positiveDeletedProjection 2 (n : ℤ)-Coeff.positiveDeletedProjection 2 (0 : ℤ)

theorem hillExtendedMixedPeriodJacobian_add_projection (N n : ℕ) (a p : Coeff 2) :
    hillExtendedMixedPeriodJacobian q hq hr h0q h0r N n a p+Coeff.positiveDeletedProjection 2 (0 : ℤ)=
      fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a+
        Coeff.positiveDeletedProjection 2 (n : ℤ) := by
  rw [hillExtendedMixedPeriodJacobian,sub_add_cancel]

private theorem eval_comp_fderiv_eq_zero_of_coordinate_zero
    (f : Coeff 2 → Coeff 2) (a : Coeff 2) (m : ℤ) (hf : DifferentiableAt ℂ f a)
    (hz : ∀ b : Coeff 2, f b m=0) :
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m).comp (fderiv ℂ f a)=0 := by
  let ev := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m
  have hE := ev.hasFDerivAt.comp a hf.hasFDerivAt
  have he : (fun b => ev (f b))=(fun _ : Coeff 2 => (0 : ℂ)) := funext hz
  simp only [Function.comp_def] at hE
  rw [he] at hE
  exact hE.unique (hasFDerivAt_const (0 : ℂ) a)

theorem hillExtendedMixedPeriodJacobian_omitted_coordinate
    (N n : ℕ) (hn : 1≤n) (a p h : Coeff 2)
    (hF : DifferentiableAt ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a) :
    hillExtendedMixedPeriodJacobian q hq hr h0q h0r N n a p h (n : ℤ)=-h (n : ℤ) := by
  have hz := eval_comp_fderiv_eq_zero_of_coordinate_zero
    (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a (n : ℤ) hF
    (fun b => hillMixedComplexPeriodSequence_apply_unsupported q hq hr h0q h0r N n hn _ (n : ℤ) (Or.inr rfl))
  have hh := congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L h) hz
  change fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N n (b,p)) a h (n : ℤ)=0 at hh
  simp only [hillExtendedMixedPeriodJacobian,add_apply,sub_apply,lp.coeFn_add,Pi.add_apply,lp.coeFn_sub,Pi.sub_apply,
    hh,Coeff.positiveDeletedProjection_apply,if_neg (by omega : ¬((0 : ℤ)<n ∧ (n : ℤ)≠n)),
    if_pos (show (0 : ℤ)<n ∧ (n : ℤ)≠0 by omega),add_zero,zero_sub]

theorem tendsto_hillExtendedMixedPeriodJacobian_row
    {ι : Type*} {l : Filter ι} (n : ι → ℕ) (hn : ∀ i, 1≤n i) (hni : Tendsto n l atTop)
    (N : ℕ) (hN : 1≤N) (B D : ℝ) (hD : 0≤D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖≤B)
    (a : ι → Coeff 2) (a0 : Coeff 2) (ha : Tendsto a l (𝓝 a0))
    (R : ℝ) (hR : 0≤R) (har : ∀ i, ‖a i‖≤R)
    (hF : ∀ i, DifferentiableAt ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N (n i) (b,SpectralWeight.one.toCoeff q)) (a i))
    (hFull : DifferentiableAt ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,SpectralWeight.one.toCoeff q)) a0)
    (m : ℤ) :
    Tendsto (fun i => (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m).comp
      (hillExtendedMixedPeriodJacobian q hq hr h0q h0r N (n i) (a i) (SpectralWeight.one.toCoeff q))) l
      (𝓝 ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m).comp
        (fderiv ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,SpectralWeight.one.toCoeff q)) a0))) := by
  let ev := lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 m
  by_cases hm : m≤0
  · have hP (j : ℕ) : ev.comp (Coeff.positiveDeletedProjection 2 (j : ℤ))=0 := by
      ext h
      change Coeff.positiveDeletedProjection 2 (j : ℤ) h m=0
      rw [Coeff.positiveDeletedProjection_apply,if_neg (by omega : ¬(0<m ∧ m≠(j : ℤ)))]
    have hfinite (i : ι) : ev.comp (hillExtendedMixedPeriodJacobian q hq hr h0q h0r N (n i) (a i) (SpectralWeight.one.toCoeff q))=0 := by
      have hz := eval_comp_fderiv_eq_zero_of_coordinate_zero
        (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N (n i) (b,SpectralWeight.one.toCoeff q)) (a i) m (hF i)
        (fun b => hillMixedComplexPeriodSequence_apply_unsupported q hq hr h0q h0r N (n i) (hn i) _ m (Or.inl hm))
      change ev.comp (fderiv ℂ (fun b : Coeff 2 =>
        hillMixedComplexPeriodSequence q hq hr h0q h0r N (n i) (b,SpectralWeight.one.toCoeff q)) (a i))=0 at hz
      have hP0 : ev.comp (Coeff.positiveDeletedProjection 2 (0 : ℤ))=0 := hP 0
      simp only [hillExtendedMixedPeriodJacobian,ContinuousLinearMap.comp_sub,ContinuousLinearMap.comp_add,
        hz,hP (n i),hP0,add_zero,sub_self]
    have hfullzero : ev.comp (fderiv ℂ (fun b : Coeff 2 =>
        hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,SpectralWeight.one.toCoeff q)) a0)=0 :=
      eval_comp_fderiv_eq_zero_of_coordinate_zero _ a0 m hFull
        (fun b => hillFullMixedComplexPeriodSequence_apply_nonpositive q hq hr h0q h0r N hN B D hD hc b _ hp m hm)
    change Tendsto (fun i => ev.comp _) l (𝓝 (ev.comp _))
    simp only [hfinite,hfullzero]
    exact tendsto_const_nhds
  · have hk : 1≤m.toNat := by omega
    have hcast : (m.toNat : ℤ)=m := by omega
    have ht := tendsto_fderiv_hillMixedPeriod_base_row q hq hr h0q h0r n hn hni N m.toNat hN hk B D hD hc hp a a0 ha R hR har hF hFull
    simp only [hcast] at ht
    apply ht.congr'
    filter_upwards [hni.eventually (eventually_gt_atTop m.toNat)] with i hi
    apply ContinuousLinearMap.ext
    intro h
    change (fderiv ℂ (fun b : Coeff 2 => hillMixedComplexPeriodSequence q hq hr h0q h0r N (n i) (b,SpectralWeight.one.toCoeff q)) (a i) h) m=
      (hillExtendedMixedPeriodJacobian q hq hr h0q h0r N (n i) (a i) (SpectralWeight.one.toCoeff q) h) m
    simp only [hillExtendedMixedPeriodJacobian,add_apply,sub_apply,lp.coeFn_add,Pi.add_apply,lp.coeFn_sub,Pi.sub_apply,
      Coeff.positiveDeletedProjection_apply,if_pos (show 0<m ∧ m≠(n i : ℤ) by omega),
      if_pos (show 0<m ∧ m≠(0 : ℤ) by omega),add_sub_cancel_right]

/-- The actual extended scaled mixed Jacobians converge in full operator
norm, along every convergent root family in a compact set and escaping
positive differential indices. -/
theorem tendsto_hillExtendedMixedPeriodJacobian
    {ι : Type*} {l : Filter ι} (n : ι → ℕ) (hn : ∀ i, 1≤n i) (hni : Tendsto n l atTop)
    (N : ℕ) (hN : 1≤N) (B D : ℝ) (hD : 0≤D)
    (hc : HillComplexTailPeriodControl h0q h0r N B D) (hp : ‖SpectralWeight.one.toCoeff q‖≤B)
    (K : Set (Coeff 2)) (hK : IsCompact K) (a : ι → Coeff 2) (haK : ∀ i, a i∈K)
    (a0 : Coeff 2) (ha : Tendsto a l (𝓝 a0))
    (hF : ∀ j : ℕ, 1≤j → AnalyticOnNhd ℂ (fun b : Coeff 2 =>
      hillMixedComplexPeriodSequence q hq hr h0q h0r N j (b,SpectralWeight.one.toCoeff q)) univ)
    (hFull : AnalyticOnNhd ℂ (fun b : Coeff 2 =>
      hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,SpectralWeight.one.toCoeff q)) univ) :
    Tendsto (fun i => hillExtendedMixedPeriodJacobian q hq hr h0q h0r N (n i) (a i) (SpectralWeight.one.toCoeff q)) l
      (𝓝 (fderiv ℂ (fun b : Coeff 2 => hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,SpectralWeight.one.toCoeff q)) a0)) := by
  have hB : 0≤B := (norm_nonneg _).trans hp
  obtain ⟨R,hR,hbound⟩ := hK.isBounded.exists_pos_norm_le
  have hcompact : IsCompactOperator (fderiv ℂ (fun b : Coeff 2 =>
      hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,SpectralWeight.one.toCoeff q)) a0-
      (-Coeff.positiveDeletedProjection 2 (0 : ℤ))) := by
    simpa only [sub_neg_eq_add] using isCompactOperator_fderiv_hillFullMixedPeriod_add_projection q hq hr h0q h0r N hN B D hD hc a0 _ hp hFull
  apply Coeff.tendsto_operator_of_rows_and_uniform_remainder_outputTails (by norm_num : (2 : ℝ≥0∞)≠⊤)
    _ _ (-Coeff.positiveDeletedProjection 2 (0 : ℤ)) hcompact
  · intro m
    exact tendsto_hillExtendedMixedPeriodJacobian_row q hq hr h0q h0r n hn hni N hN B D hD hc hp a a0 ha R hR.le
      (fun i => hbound _ (haK i)) (fun i => (hF _ (hn i) _ (mem_univ _)).differentiableAt)
      (hFull _ (mem_univ _)).differentiableAt m
  · intro ε hε
    obtain ⟨s,hs⟩ := exists_fderiv_hillMixedPeriod_add_projection_uniform_outputTail q hq hr h0q h0r
      N B D hB hD hc {SpectralWeight.one.toCoeff q} (fun p hp' => by simpa only [mem_singleton_iff.mp hp'] using hp)
      (fun j hj p hp' => by simpa only [mem_singleton_iff.mp hp'] using hF j hj) K hK ε hε
    refine ⟨s,?_⟩
    intro t hst
    exact Eventually.of_forall fun i => by
      simpa only [sub_neg_eq_add,hillExtendedMixedPeriodJacobian,sub_add_cancel] using
        hs t hst (n i) (hn i) (a i) (haK i) _ (mem_singleton _)

/-- All analytic hypotheses of the full Jacobian norm limit hold on one
original complex source neighborhood, independently of the deleted index. -/
theorem exists_hillExtendedMixedPeriodJacobian_norm_limit
    (K : Set (Coeff 2)) (hK : IsCompact K) :
    ∃ N : ℕ, ∃ B D : ℝ, ∃ U : Set (Coeff 2),
      1≤N ∧ 0<B ∧ 0<D ∧ HillComplexTailPeriodControl h0q h0r N B D ∧
        IsOpen U ∧ SpectralWeight.one.toCoeff q∈U ∧ U⊆ball 0 B ∧
        AnalyticOnNhd ℂ (hillFullMixedComplexPeriodSequence q hq hr h0q h0r N) (univ ×ˢ U) ∧
        (∀ j : ℕ, 1≤j → AnalyticOnNhd ℂ (hillMixedComplexPeriodSequence q hq hr h0q h0r N j) (univ ×ˢ U)) ∧
        ∀ n : ℕ → ℕ, (∀ i, 1≤n i) → Tendsto n atTop atTop →
          ∀ a : ℕ → Coeff 2, (∀ i, a i∈K) → ∀ a0 : Coeff 2, Tendsto a atTop (𝓝 a0) →
          Tendsto (fun i => hillExtendedMixedPeriodJacobian q hq hr h0q h0r N (n i) (a i) (SpectralWeight.one.toCoeff q)) atTop
            (𝓝 (fderiv ℂ (fun b : Coeff 2 =>
              hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,SpectralWeight.one.toCoeff q)) a0)) := by
  obtain ⟨N,B,D,U,hN,hD,hc,hU,hqU,hsub,hA⟩ :=
    exists_hillMixedComplexPeriodSequence_analytic_neighborhood q hq hr h0q h0r
  obtain ⟨V,hV,hqV,hP⟩ := exists_hillAbelianProductComplexPeriods_common_finite_neighborhood q hq hr N
  have hp : ‖SpectralWeight.one.toCoeff q‖<B := by simpa only [mem_ball,dist_zero_right] using hsub hqU
  have hB : 0<B := (norm_nonneg _).trans_lt hp
  let W := U∩V
  have hqW : SpectralWeight.one.toCoeff q∈W := ⟨hqU,hqV⟩
  have hFull : AnalyticOnNhd ℂ (hillFullMixedComplexPeriodSequence q hq hr h0q h0r N) (univ ×ˢ W) := by
    apply (analyticOnNhd_hillFullMixedComplexPeriodSequence q hq hr h0q h0r N hN B D hB hD.le hc V (hP 0)).mono
    intro t ht
    exact ⟨mem_univ _,ht.2.2,hsub ht.2.1⟩
  have hFinite : ∀ j : ℕ, 1≤j → AnalyticOnNhd ℂ
      (hillMixedComplexPeriodSequence q hq hr h0q h0r N j) (univ ×ˢ W) :=
    fun j hj => (hA j hj).mono (fun _ ht => ⟨mem_univ _,ht.2.1⟩)
  have hfullsec : AnalyticOnNhd ℂ (fun b : Coeff 2 =>
      hillFullMixedComplexPeriodSequence q hq hr h0q h0r N (b,SpectralWeight.one.toCoeff q)) univ := by
    intro b _
    exact (hFull (b,SpectralWeight.one.toCoeff q) ⟨mem_univ _,hqW⟩).comp
      (f := fun b : Coeff 2 => (b,SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)
  have hfinitesec : ∀ j : ℕ, 1≤j → AnalyticOnNhd ℂ (fun b : Coeff 2 =>
      hillMixedComplexPeriodSequence q hq hr h0q h0r N j (b,SpectralWeight.one.toCoeff q)) univ := by
    intro j hj b _
    exact (hFinite j hj (b,SpectralWeight.one.toCoeff q) ⟨mem_univ _,hqW⟩).comp
      (f := fun b : Coeff 2 => (b,SpectralWeight.one.toCoeff q)) (analyticAt_id.prod analyticAt_const)
  refine ⟨N,B,D,W,hN,hB,hD,hc,hU.inter hV,hqW,fun p hpW => hsub hpW.1,hFull,hFinite,?_⟩
  intro n hn hni a haK a0 ha
  exact tendsto_hillExtendedMixedPeriodJacobian q hq hr h0q h0r n hn hni N hN B D hD.le hc hp.le
    K hK a haK a0 ha hfinitesec hfullsec

end NLS.KdV
