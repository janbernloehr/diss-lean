import NLS.Articles.KdVPseudomeasures.OriginalHillActionShortArc
import NLS.Articles.KdVPseudomeasures.OriginalHillPhysicalLocalHomeomorph
import NLS.Topology.LocalInverseLift

/-! The ACTUAL native local inverse maps nearby points of the SAME action
torus into the SAME original isospectral set, including infinite-support
tori. Finite short action arcs remain in the chosen inverse chart; norm
limits retain the original compact isospectral fiber. -/
noncomputable section
open Set Complex Filter Topology Metric NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

/-- Every finite symmetric target replacement has an actual isospectral
preimage on the SPECIFIED local inverse branch. The fixed target ball and
full-target distance bound precede every finite block. -/
theorem exists_isospectral_local_inverse_finite_replacement
    (q : HillRealMeanZeroSource) (e : OpenPartialHomeomorph HillRealSignedTarget HillRealMeanZeroSource)
    (he : (e.symm : HillRealMeanZeroSource → HillRealSignedTarget)=hillRealSignedMap)
    (heq : e (hillRealSignedMap q)=q) (r : ℝ)
    (hball : ball (hillRealSignedMap q) r ⊆ e.source)
    (z : HillRealSignedTarget) (hz : z ∈ hillRealNativeActionTorus q)
    (hzr : ‖z-hillRealSignedMap q‖<r) (N : ℕ) :
    ∃ p : HillRealMeanZeroSource, hillRealDiscriminantData p=hillRealDiscriminantData q ∧
      hillRealSignedMap p=WeightedCoeff.fourierRealZeroReplace (Weight.signedSobolev (-1/2)) (N+1) (hillRealSignedMap q) z ∧
      e (hillRealSignedMap p)=p := by
  let a := hillRealSignedMap q
  induction N with
  | zero =>
    refine ⟨q,rfl,?_,heq⟩
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
    obtain ⟨p,hpiso,hp,hpe⟩ := ih
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
    refine ⟨b,(originalHillNativeActionFlow_conserved n p θ).trans hpiso,?_,hbe⟩
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

/-- The FULL infinite-support actual action torus is preserved by a nearby
specified native inverse branch. Neither global injectivity nor global
properness nor connectedness of a Miura slice is assumed. -/
theorem hillNative_local_inverse_isospectral (q : HillRealMeanZeroSource) :
    ∃ r : ℝ, 0<r ∧ ∀ z : HillRealSignedTarget, z ∈ hillRealNativeActionTorus q →
      ‖z-hillRealSignedMap q‖<r →
      hillRealDiscriminantData (hillPhysicalNativeMap_isLocalHomeomorph.localInverseAt q z)=
        hillRealDiscriminantData q := by
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
  apply (isCompact_hillRealDiscriminant_fiber q).isClosed.mem_of_tendsto (hc.tendsto.comp ht)
  apply Eventually.of_forall
  intro N
  obtain ⟨p,hp,hpz,hpe⟩ := exists_isospectral_local_inverse_finite_replacement q e
    (hillPhysicalNativeMap_isLocalHomeomorph.localInverseAt_symm q)
    (hillPhysicalNativeMap_isLocalHomeomorph.localInverseAt_apply_self) r hball z hz hzr N
  change hillRealDiscriminantData (e (zN N))=hillRealDiscriminantData q
  dsimp only [zN]
  rw [← hpz,hpe]
  exact hp


/-- Near EVERY actual native source, equality of ALL actions is exactly
membership in its original isospectral fiber, including collapsed gaps
and infinite-support action tori. The neighborhood uses the original
Hminus-one source topology. -/
theorem exists_open_action_level_eq_isospectral (q : HillRealMeanZeroSource) :
    ∃ U : Set HillRealMeanZeroSource, IsOpen U ∧ q ∈ U ∧
      ∀ p ∈ U, hillRealSignedMap p ∈ hillRealNativeActionTorus q ↔
        hillRealDiscriminantData p=hillRealDiscriminantData q := by
  obtain ⟨r,hr,hriso⟩ := hillNative_local_inverse_isospectral q
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
  · intro p hp
    constructor
    · intro hpa
      have he : e (hillRealSignedMap p)=p := by
        have h := e.right_inv hp.1
        rw [hillPhysicalNativeMap_isLocalHomeomorph.localInverseAt_symm] at h
        exact h
      have hnorm : dist (hillRealSignedMap p) (hillRealSignedMap q)<r := hp.2
      rw [dist_eq_norm] at hnorm
      have h := hriso (hillRealSignedMap p) hpa (by convert hnorm using 1; rfl)
      change hillRealDiscriminantData (e (hillRealSignedMap p))=hillRealDiscriminantData q at h
      rwa [he] at h
    · exact hillRealSignedMap_mem_actionTorus_of_discriminant_eq p q

end NLS.Articles.KdVPseudomeasures
