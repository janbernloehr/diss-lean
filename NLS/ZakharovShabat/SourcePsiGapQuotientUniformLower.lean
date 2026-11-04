import NLS.ZakharovShabat.SourcePsiQuotientUniformGapProductTail
import NLS.ZakharovShabat.SourcePsiDeletedProductNonzero
import NLS.ZakharovShabat.SourcePsiIndexRatioUniformLower
import NLS.ZakharovShabat.SourceFiniteGapExterior

/-! The literal omitted-root quotient has one positive lower norm
bound on EVERY actual selected gap, uniformly over the full real gap
product and all signed indices, including low and collapsed gaps. -/
noncomputable section
open Set Metric Complex
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem SourceIsolatingNeighborhoods.gap_quotient_lower_at_index
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {C : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D C)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (hreal : IsRealType (CoeffPair.toMax p ψ)) (m : ℤ) :
    ∃ c : ℝ, 0 < c ∧ ∀ a ∈ sourcePeriodicGapRootSet hp hp1 ψ,
      ∀ z ∈ sourcePeriodicSegment hp hp1 ψ m,
        c ≤ ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ))‖ := by
  obtain ⟨W,_,_,hR,hQ⟩ := exists_global_source_analytic_singleRootQuotient hp hp1
  have hdom (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 ψ m) :
      z ∈ sourceStandardRootOmittedDomain hp hp1 ψ m := by
    intro k hkm hzk
    exact Set.disjoint_left.mp (hD.disjoint m k hkm.symm) (hD.gap ψ hψ m hz) (hD.gap ψ hψ k hzk)
  let K := sourcePeriodicGapRootSet hp hp1 ψ ×ˢ sourcePeriodicSegment hp hp1 ψ m
  have hK : IsCompact K := (isCompact_sourcePeriodicGapRootSet hp hp1 ψ).prod
    (isCompact_sourcePeriodicSegment hp hp1 ψ m)
  let F : Coeff p × ℂ → ℂ := fun t => sourceSingleRootQuotientJointProduct hp hp1 m (t.2,(t.1,ψ))
  have hcont : ContinuousOn F K := by
    intro t ht
    have hi : Continuous (fun s : Coeff p × ℂ => (s.2,(s.1,ψ))) := by fun_prop
    exact (((hQ m).2 (t.2,(t.1,ψ)) ⟨hR hreal,hdom t.2 ht.2⟩).continuousAt.comp
      (x := t) (f := fun s : Coeff p × ℂ => (s.2,(s.1,ψ))) hi.continuousAt).continuousWithinAt
  have hne (t : Coeff p × ℂ) (ht : t ∈ K) : F t ≠ 0 := by
    apply sourceSingleRootQuotientJointProduct_ne_zero_of_off_other hp hp1 m t.2 t.1 ψ ?_ (hdom t.2 ht.2)
    intro k hkm he
    have hk : t.2 ∈ D k := by rw [he]; exact hD.gap ψ hψ k (ht.1 k)
    exact Set.disjoint_left.mp (hD.disjoint m k hkm.symm) (hD.gap ψ hψ m ht.2) hk
  obtain ⟨c,hc,hbound⟩ := hK.exists_forall_le' hcont.norm (fun t ht => norm_pos_iff.mpr (hne t ht))
  exact ⟨c,hc,fun a ha z hz => hbound (a,z) ⟨ha,hz⟩⟩

theorem SourceIsolatingNeighborhoods.gap_quotient_finiteHead_lower
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {C : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D C)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (hreal : IsRealType (CoeffPair.toMax p ψ)) (s : Finset ℤ) :
    ∃ c : ℝ, 0 < c ∧ ∀ m ∈ s, ∀ a ∈ sourcePeriodicGapRootSet hp hp1 ψ,
      ∀ z ∈ sourcePeriodicSegment hp hp1 ψ m,
        c ≤ ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ))‖ := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert m s hm ih =>
    obtain ⟨c,hc,hcs⟩ := ih
    obtain ⟨b,hb,hbm⟩ := hD.gap_quotient_lower_at_index ψ hψ hreal m
    refine ⟨min c b,lt_min hc hb,?_⟩
    intro k hk a ha z hz
    rcases Finset.mem_insert.mp hk with rfl | hks
    · exact (min_le_right _ _).trans (hbm a ha z hz)
    · exact (min_le_left _ _).trans (hcs k hks a ha z hz)

theorem SourceIsolatingNeighborhoods.gap_quotient_uniform_lower
    {hp : p ≠ ⊤} {hp1 : 1 < p} {V : Set (CoeffPair p)}
    {D : ℤ → Set ℂ} {C : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D C)
    (ψ : CoeffPair p) (hψ : ψ ∈ V) (hreal : IsRealType (CoeffPair.toMax p ψ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ a ∈ sourcePeriodicGapRootSet hp hp1 ψ,
      ∀ m : ℤ, ∀ z ∈ sourcePeriodicSegment hp hp1 ψ m,
        c ≤ ‖sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ))‖ := by
  obtain ⟨δ,hδ,N,hN⟩ := exists_sourcePsiQuotient_uniformSmallTail_near_gapProduct hp hp1
    (⟨ψ,hreal⟩:realTypeSourceLocus p) (1/2) (by norm_num)
  let s : Finset ℤ := Finset.Icc (-(N:ℤ)) (N:ℤ)
  obtain ⟨c,hc,hhead⟩ := hD.gap_quotient_finiteHead_lower ψ hψ hreal s
  refine ⟨min (1/2) c,lt_min (by norm_num) hc,?_⟩
  intro a ha m z hz
  by_cases hm : N ≤ m.natAbs
  · have ht : (a,ψ) ∈ cthickening δ (sourcePeriodicGapRootSet hp hp1 ψ ×ˢ {ψ}) :=
      mem_cthickening_of_dist_le (a,ψ) (a,ψ) δ _ ⟨ha,mem_singleton ψ⟩ (by simpa only [dist_self] using hδ.le)
    have hq := hN (a,ψ) ht m hm
    have he := hq.2 z (ball_subset_closedBall (hq.1 hz))
    have htri := norm_le_norm_sub_add (1:ℂ) (sourceSingleRootQuotientJointProduct hp hp1 m (z,(a,ψ)))
    rw [norm_one,norm_sub_rev] at htri
    exact (min_le_left _ _).trans (by linarith)
  · have hms : m ∈ s := by simp only [s,Finset.mem_Icc]; omega
    exact (min_le_right _ _).trans (hhead m hms a ha z hz)

end NLS.ZakharovShabat
