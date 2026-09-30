import NLS.ComplexAnalysis.CompactNonzeroLowerBound
import NLS.ZakharovShabat.SourcePsiGapProductCompact
import NLS.ZakharovShabat.SourcePsiDeletedProductNonzero
import NLS.ZakharovShabat.SourceCanonicalRootGapIsolation
import NLS.ZakharovShabat.SourcePeriodicMidpointGapContinuity

/-!
# Uniform finite-head midpoint quotient lower bounds near the gap product

The actual regular quotient is nonzero at a selected real midpoint
for every full gap-root vector. Joint analyticity and midpoint
continuity give continuity on the compact gap product times the
reference source. A finite family of selected indices therefore has
one positive lower bound on a common metric neighborhood of that
entire compact set, ready for all midpoint-filled analytic branches.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Any finite family of midpoint quotient values stays bounded
away from zero near the entire compact real gap-root product and
reference source, without restricting the omitted root index. -/
theorem exists_sourcePsi_midpointQuotient_finiteHead_lowerBound_near_gapProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceLocus p) (s : Finset ℤ) :
    ∃ δ c : ℝ, 0 < δ ∧ 0 < c ∧
      ∀ t ∈ cthickening δ (sourcePeriodicGapRootSet hp hp1 φ.val ×ˢ {φ.val}),
        ∀ m ∈ s, c ≤ ‖sourceSingleRootQuotientJointProduct hp hp1 m
          (sourceStandardRootMidpoint hp hp1 t.2 m,t)‖ := by
  obtain ⟨W,hW,_,hreal,hQ⟩ := exists_global_source_analytic_singleRootQuotient hp hp1
  obtain ⟨U,_,_,hrealU,hdisjoint⟩ := exists_global_source_disjoint_periodicSegments hp hp1
  have hφW : φ.val ∈ W := hreal φ.property
  have hφU : φ.val ∈ U := hrealU φ.property
  have hτ m : sourceStandardRootMidpoint hp hp1 φ.val m ∈ sourcePeriodicSegment hp hp1 φ.val m :=
    sourcePeriodicMidpoint_mem_segment hp hp1 φ.val m
  have hdom m : sourceStandardRootMidpoint hp hp1 φ.val m ∈ sourceStandardRootOmittedDomain hp hp1 φ.val m := by
    intro k hkm hk
    exact Set.disjoint_left.mp (hdisjoint φ.val hφU m k hkm.symm) (hτ m) hk
  let K := sourcePeriodicGapRootSet hp hp1 φ.val ×ˢ {φ.val}
  let F : ℤ → (Coeff p × CoeffPair p) → ℂ := fun m t =>
    sourceSingleRootQuotientJointProduct hp hp1 m (sourceStandardRootMidpoint hp hp1 t.2 m,t)
  have hK : IsCompact K := (isCompact_sourcePeriodicGapRootSet hp hp1 φ.val).prod isCompact_singleton
  have hcont m (t : Coeff p × CoeffPair p) (ht : t ∈ K) : ContinuousAt (F m) t := by
    rcases t with ⟨a,ψ⟩
    have hψ : ψ = φ.val := ht.2
    subst ψ
    have hmid : ContinuousAt (fun χ : CoeffPair p => sourceStandardRootMidpoint hp hp1 χ m) φ.val := by
      have hL := continuousAt_canonicalPeriodicLeft_periodOne_of_realType hp hp1 φ.val φ.property m
      have hR := continuousAt_canonicalPeriodicRight_periodOne_of_realType hp hp1 φ.val φ.property m
      exact (hL.add hR).div_const (2 : ℂ)
    have hmidPair : ContinuousAt (fun q : Coeff p × CoeffPair p =>
        sourceStandardRootMidpoint hp hp1 q.2 m) (a,φ.val) :=
      hmid.comp (x := (a,φ.val)) (f := Prod.snd) continuousAt_snd
    have hinc : ContinuousAt (fun q : Coeff p × CoeffPair p =>
        (sourceStandardRootMidpoint hp hp1 q.2 m,q)) (a,φ.val) :=
      hmidPair.prodMk continuousAt_id
    have hbasepoint : (sourceStandardRootMidpoint hp hp1 φ.val m,(a,φ.val)) ∈
        sourceSingleRootQuotientJointDomain hp hp1 W m := ⟨hφW,hdom m⟩
    exact ((hQ m).2 _ hbasepoint).continuousAt.comp (x := (a,φ.val))
      (f := fun q : Coeff p × CoeffPair p => (sourceStandardRootMidpoint hp hp1 q.2 m,q)) hinc
  have hnonzero m (t : Coeff p × CoeffPair p) (ht : t ∈ K) : F m t ≠ 0 := by
    rcases t with ⟨a,ψ⟩
    have hψ : ψ = φ.val := ht.2
    subst ψ
    apply sourceSingleRootQuotientJointProduct_ne_zero_of_off_other hp hp1 m _ a φ.val ?_ (hdom m)
    intro k hkm heq
    have hk : sourceStandardRootMidpoint hp hp1 φ.val m ∈ sourcePeriodicSegment hp hp1 φ.val k := by
      rw [heq]
      exact ht.1 k
    exact Set.disjoint_left.mp (hdisjoint φ.val hφU m k hkm.symm) (hτ m) hk
  exact NLS.ComplexAnalysis.exists_finiteFamily_positive_lower_bound_on_cthickening K hK s F
    (fun m _ => hcont m) (fun m _ => hnonzero m)

end NLS.ZakharovShabat
