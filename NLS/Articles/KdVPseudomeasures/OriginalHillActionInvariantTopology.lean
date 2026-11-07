import NLS.Articles.KdVPseudomeasures.OriginalHillLocalIsospectralInverse
import NLS.Topology.LocalConstancyAlong

/-! Closed sets invariant under all actual complete indexed action flows
contain a relative neighborhood in the original isospectral fiber at every
one of their points. This includes infinite-support action tori. -/
noncomputable section
open Set Complex Filter Topology Metric NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

/-- Finite target matching retains ANY set invariant under actual action flows. -/
theorem exists_action_invariant_finite_replacement
    (q : HillRealMeanZeroSource) (S : Set HillRealMeanZeroSource) (hq : q ∈ S)
    (hflow : ∀ n : ℕ+, ∀ p ∈ S, ∀ t : ℝ, originalHillNativeActionFlow n p t ∈ S)
    (e : OpenPartialHomeomorph HillRealSignedTarget HillRealMeanZeroSource)
    (he : (e.symm : HillRealMeanZeroSource → HillRealSignedTarget)=hillRealSignedMap)
    (heq : e (hillRealSignedMap q)=q) (r : ℝ)
    (hball : ball (hillRealSignedMap q) r ⊆ e.source)
    (z : HillRealSignedTarget) (hz : z ∈ hillRealNativeActionTorus q)
    (hzr : ‖z-hillRealSignedMap q‖<r) (N : ℕ) :
    ∃ p : HillRealMeanZeroSource, p ∈ S ∧
      hillRealSignedMap p=WeightedCoeff.fourierRealZeroReplace (Weight.signedSobolev (-1/2)) (N+1) (hillRealSignedMap q) z ∧
      e (hillRealSignedMap p)=p := by
  let a := hillRealSignedMap q
  induction N with
  | zero =>
    refine ⟨q,hq,?_,heq⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext k
    rw [WeightedCoeff.fourierRealZeroReplace_apply]
    by_cases hk : k=0
    · subst k
      rw [show a.val.val.val 0=0 from a.val.property,show z.val.val.val 0=0 from z.val.property]
      simp
    · rw [if_neg (by have := Int.natAbs_pos.mpr hk; omega)]
  | succ N ih =>
    obtain ⟨p,hpS,hp,hpe⟩ := ih
    let n : ℕ+ := ⟨N+1,by omega⟩
    have ha : (hillRealSignedMap p).val.val.val (n:ℤ)=a.val.val.val (n:ℤ) := by
      rw [hp,WeightedCoeff.fourierRealZeroReplace_apply,Int.natAbs_natCast,if_neg (by change ¬N+1<N+1; omega)]
    have hdom (k : ℤ) : ‖(hillRealSignedMap p).val.val.val k-a.val.val.val k‖ ≤ ‖z.val.val.val k-a.val.val.val k‖ := by
      rw [hp,WeightedCoeff.fourierRealZeroReplace_apply]
      split_ifs
      · exact le_rfl
      · change ‖a.val.val.val k-a.val.val.val k‖ ≤ ‖z.val.val.val k-a.val.val.val k‖
        rw [sub_self,norm_zero]
        exact norm_nonneg _
    obtain ⟨θ,_,hend,hpath⟩ := exists_short_action_output_path n p a z ha (norm_actionTorus_positive q z hz n) hdom
    let γ : ℝ → HillRealMeanZeroSource := fun u => originalHillNativeActionFlow n p (u*θ)
    have hc : Continuous γ := (continuous_originalHillNativeActionFlow n p).comp (continuous_id.mul continuous_const)
    have hm (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : hillRealSignedMap (γ u) ∈ e.source := by
      apply hball
      rw [mem_ball,dist_eq_norm]
      exact (hpath u hu).trans_lt hzr
    have hzero : e (hillRealSignedMap (γ 0))=γ 0 := by
      simpa only [γ,zero_mul,originalHillNativeActionFlow_zero] using hpe
    have hl := NLS.Topology.eqOn_localInverse_lift hillRealSignedMap hillPhysicalNativeMap_isLocalHomeomorph
      e he (Icc (0:ℝ) 1) isPreconnected_Icc γ hc.continuousOn hm 0 (by constructor <;> norm_num) hzero
    let b := originalHillNativeActionFlow n p θ
    have hbe : e (hillRealSignedMap b)=b := by
      simpa only [γ,one_mul,b] using hl (show (1:ℝ) ∈ Icc 0 1 by constructor <;> norm_num)
    have hpos : (hillRealSignedMap b).val.val.val (n:ℤ)=
        (WeightedCoeff.fourierRealZeroReplace (Weight.signedSobolev (-1/2)) (N+1+1) a z).val.val.val (n:ℤ) := by
      rw [WeightedCoeff.fourierRealZeroReplace_apply,Int.natAbs_natCast,if_pos (by change N+1<N+1+1; omega)]
      exact hend
    refine ⟨b,hflow n p hpS θ,?_,hbe⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    funext k
    by_cases hkp : k=(n:ℤ)
    · subst k
      exact hpos
    · by_cases hkn : k= -(n:ℤ)
      · subst k
        rw [(hillRealSignedMap b).property,
          (WeightedCoeff.fourierRealZeroReplace (Weight.signedSobolev (-1/2)) (N+1+1) a z).property]
        exact congrArg (starRingEnd ℂ) hpos
      · have habs : k.natAbs ≠ N+1 := by
          intro h
          rcases Int.natAbs_eq_iff.mp h with h | h
          · exact hkp h
          · exact hkn h
        change (hillRealSignedMap (originalHillNativeActionFlow n p θ)).val.val.val k= _
        rw [hillRealSignedMap_actionFlow_apply,hillActionRotationRate,if_neg hkp,if_neg hkn,
          zero_mul,exp_zero,one_mul,hp,WeightedCoeff.fourierRealZeroReplace_apply,
          WeightedCoeff.fourierRealZeroReplace_apply]
        have hi : k.natAbs<N+1 ↔ k.natAbs<N+1+1 := by omega
        simp only [hi]

/-- A specified local inverse retains every closed action-invariant set
near any one of its points, on the SAME full original action torus. -/
theorem hillNative_local_inverse_mem_closed_action_invariant
    (q : HillRealMeanZeroSource) (S : Set HillRealMeanZeroSource) (hS : IsClosed S) (hq : q ∈ S)
    (hflow : ∀ n : ℕ+, ∀ p ∈ S, ∀ t : ℝ, originalHillNativeActionFlow n p t ∈ S) :
    ∃ r : ℝ, 0<r ∧ ∀ z : HillRealSignedTarget, z ∈ hillRealNativeActionTorus q →
      ‖z-hillRealSignedMap q‖<r →
      hillPhysicalNativeMap_isLocalHomeomorph.localInverseAt q z ∈ S := by
  let e := hillPhysicalNativeMap_isLocalHomeomorph.localInverseAt q
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    (e.open_source.mem_nhds hillPhysicalNativeMap_isLocalHomeomorph.apply_self_mem_localInverseAt_source)
  refine ⟨r,hr,fun z hz hzr => ?_⟩
  let zN : ℕ → HillRealSignedTarget := fun N =>
    WeightedCoeff.fourierRealZeroReplace (Weight.signedSobolev (-1/2)) (N+1) (hillRealSignedMap q) z
  have hidx : Tendsto (fun N : ℕ => N+1) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with c hc
    omega
  have ht : Tendsto zN atTop (𝓝 z) :=
    (WeightedCoeff.tendsto_fourierRealZeroReplace (by norm_num : (2:ℝ≥0∞) ≠ ⊤)
      (Weight.signedSobolev (-1/2)) (hillRealSignedMap q) z).comp hidx
  have hzE : z ∈ e.source := hball (by rw [mem_ball,dist_eq_norm]; exact hzr)
  have hc : ContinuousAt e z := (e.continuousOn z hzE).continuousAt (e.open_source.mem_nhds hzE)
  apply hS.mem_of_tendsto (hc.tendsto.comp ht)
  apply Eventually.of_forall
  intro N
  obtain ⟨p,hp,hpz,hpe⟩ := exists_action_invariant_finite_replacement q S hq hflow e
    (hillPhysicalNativeMap_isLocalHomeomorph.localInverseAt_symm q)
    (hillPhysicalNativeMap_isLocalHomeomorph.localInverseAt_apply_self) r hball z hz hzr N
  change e (zN N) ∈ S
  dsimp only [zN]
  rw [← hpz,hpe]
  exact hp

/-- Every closed action-invariant set contains a relatively open
neighborhood in the original isospectral fiber at each of its points. -/
theorem exists_open_isospectral_subset_closed_action_invariant
    (q : HillRealMeanZeroSource) (S : Set HillRealMeanZeroSource) (hS : IsClosed S) (hq : q ∈ S)
    (hflow : ∀ n : ℕ+, ∀ p ∈ S, ∀ t : ℝ, originalHillNativeActionFlow n p t ∈ S) :
    ∃ U : Set HillRealMeanZeroSource, IsOpen U ∧ q ∈ U ∧
      ∀ p ∈ U, hillRealDiscriminantData p=hillRealDiscriminantData q → p ∈ S := by
  obtain ⟨r,hr,hrS⟩ := hillNative_local_inverse_mem_closed_action_invariant q S hS hq hflow
  let e := hillPhysicalNativeMap_isLocalHomeomorph.localInverseAt q
  have hc : Continuous hillRealSignedMap := continuous_iff_continuousAt.mpr
    (fun p => (analyticAt_hillRealSignedMap p).continuousAt)
  refine ⟨e.target ∩ hillRealSignedMap ⁻¹' ball (hillRealSignedMap q) r,
    e.open_target.inter (isOpen_ball.preimage hc),?_,?_⟩
  · constructor
    · exact hillPhysicalNativeMap_isLocalHomeomorph.self_mem_localInverseAt_target
    · change dist (hillRealSignedMap q) (hillRealSignedMap q)<r
      rw [dist_self]
      exact hr
  · intro p hp hdis
    have he : e (hillRealSignedMap p)=p := by
      have h := e.right_inv hp.1
      rw [hillPhysicalNativeMap_isLocalHomeomorph.localInverseAt_symm] at h
      exact h
    have hnorm : dist (hillRealSignedMap p) (hillRealSignedMap q)<r := hp.2
    rw [dist_eq_norm] at hnorm
    have h := hrS (hillRealSignedMap p)
      (hillRealSignedMap_mem_actionTorus_of_discriminant_eq p q hdis) (by convert hnorm using 1; rfl)
    change e (hillRealSignedMap p) ∈ S at h
    rwa [he] at h

/-- Every continuous action-flow invariant is locally constant along the
original isospectral fiber. Continuity is required ONLY on that fiber. -/
theorem exists_open_action_invariant_locally_constant_on_isoset
    {Y : Type*} [TopologicalSpace Y] [T1Space Y]
    (q : HillRealMeanZeroSource) (F : HillRealMeanZeroSource → Y)
    (hc : ContinuousOn F {p | hillRealDiscriminantData p=hillRealDiscriminantData q})
    (hi : ∀ n : ℕ+, ∀ p : HillRealMeanZeroSource,
      hillRealDiscriminantData p=hillRealDiscriminantData q →
      ∀ t : ℝ, F (originalHillNativeActionFlow n p t)=F p) :
    ∃ U : Set HillRealMeanZeroSource, IsOpen U ∧ q ∈ U ∧
      ∀ p ∈ U, hillRealDiscriminantData p=hillRealDiscriminantData q → F p=F q := by
  let S := {p : HillRealMeanZeroSource | hillRealDiscriminantData p=hillRealDiscriminantData q} ∩ F ⁻¹' {F q}
  have hS : IsClosed S := hc.preimage_isClosed_of_isClosed
    (isCompact_hillRealDiscriminant_fiber q).isClosed isClosed_singleton
  have hq : q ∈ S := ⟨rfl,rfl⟩
  have hf (n : ℕ+) (p : HillRealMeanZeroSource) (hp : p ∈ S) (t : ℝ) :
      originalHillNativeActionFlow n p t ∈ S := by
    refine ⟨(originalHillNativeActionFlow_conserved n p t).trans hp.1,?_⟩
    change F (originalHillNativeActionFlow n p t)=F q
    exact (hi n p hp.1 t).trans hp.2
  obtain ⟨U,hU,hqU,hUS⟩ := exists_open_isospectral_subset_closed_action_invariant q S hS hq hf
  exact ⟨U,hU,hqU,fun p hp hdis => (hUS p hp hdis).2⟩


/-- Every continuous action-flow invariant is constant along every
continuous preconnected family in the SAME original isospectral fiber.
Global connectedness of that fiber is not assumed. -/
theorem action_invariant_eq_along_isospectral_family
    {Y A : Type*} [TopologicalSpace Y] [T1Space Y] [TopologicalSpace A] [PreconnectedSpace A]
    (q : HillRealMeanZeroSource) (F : HillRealMeanZeroSource → Y)
    (hc : ContinuousOn F {p | hillRealDiscriminantData p=hillRealDiscriminantData q})
    (hi : ∀ n : ℕ+, ∀ p : HillRealMeanZeroSource,
      hillRealDiscriminantData p=hillRealDiscriminantData q →
      ∀ t : ℝ, F (originalHillNativeActionFlow n p t)=F p)
    (γ : A → HillRealMeanZeroSource) (hγ : Continuous γ)
    (hdis : ∀ a, hillRealDiscriminantData (γ a)=hillRealDiscriminantData q) (a b : A) :
    F (γ a)=F (γ b) := by
  apply NLS.Topology.eq_along_continuous_of_relative_local_constancy
    {p | hillRealDiscriminantData p=hillRealDiscriminantData q} F ?_ γ hγ hdis a b
  intro x hx
  have hc' : ContinuousOn F {p | hillRealDiscriminantData p=hillRealDiscriminantData x} := by
    rwa [hx]
  obtain ⟨U,hU,hxU,hconst⟩ := exists_open_action_invariant_locally_constant_on_isoset x F hc'
    (fun n p hp t => hi n p (hp.trans hx) t)
  exact ⟨U,hU,hxU,fun y hy hdy => hconst y hy (hdy.trans hx.symm)⟩

end NLS.Articles.KdVPseudomeasures
