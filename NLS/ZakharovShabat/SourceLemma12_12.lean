import NLS.ZakharovShabat.SourcePsiOriginalRootBootstrap

/-!
# Lemma 12.12 on exactly the domain and family of Lemmas 12.10 and 12.11

The actual filled roots differ from the moving midpoints by squared gaps
times an lp sequence. One positive bound for its literal p-power sum works
for all omitted indices on a neighborhood of every complex source. The
construction retains the preceding normalization and all original data.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The original-domain root asymptotic, retaining the exact preceding family and periods. -/
structure SourceLemma12_12Data (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W₀ W : Set (CoeffPair p)) (s : (n : ℤ) → CoeffPair p → DeletedCoeff p n) : Prop where
  previous : SourceLemma12_11Data hp hp1 W₀ W s
  offsets : ∀ ψ ∈ W, ∃ U : Set (CoeffPair p), IsOpen U ∧ ψ ∈ U ∧ U ⊆ W ∧
    ∃ C : ℝ, 0 < C ∧ ∀ χ ∈ U, ∀ n : ℤ, ∃ α : Coeff p, α n = 0 ∧
      (∀ m, displacedRoots (sourcePsiFillDeletedRoot n (s n χ)
        (sourceStandardRootMidpoint hp hp1 χ n)) m =
          sourceStandardRootMidpoint hp hp1 χ m+(sourcePeriodicGapDisplacement hp hp1 χ m)^2*α m) ∧
      Summable (fun m : ℤ => ‖α m‖^p.toReal) ∧ (∑' m : ℤ, ‖α m‖^p.toReal) ≤ C

/-- The source's two substitutions give the literal p-power bound without changing W or s. -/
theorem SourceLemma12_11Data.lemma12_12
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_11Data hp hp1 W₀ W s) (hW₀ : IsOpen W₀) :
    SourceLemma12_12Data hp hp1 W₀ W s := by
  refine ⟨H,?_⟩
  intro ψ hψ
  have hpr : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  obtain ⟨U,hU,hψU,hUW,L,hL,hb⟩ := H.original_two_stage_offsets hW₀ ψ hψ
  refine ⟨U,hU,hψU,hUW,L^p.toReal,Real.rpow_pos_of_pos hL _,?_⟩
  intro χ hχ n
  obtain ⟨β,α,_,hαn,_,hfactor,_,hα⟩ := hb χ hχ n
  refine ⟨α,hαn,hfactor,(lp.memℓp α).summable hpr,?_⟩
  rw [← lp.norm_rpow_eq_tsum hpr α]
  exact Real.rpow_le_rpow (norm_nonneg _) hα hpr.le

/-- A collapsed complex gap forces the actual root to equal its midpoint. -/
theorem SourceLemma12_12Data.collapsed_root_eq_midpoint
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_12Data hp hp1 W₀ W s) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n m : ℤ) (hgap : sourcePeriodicGapDisplacement hp hp1 ψ m = 0) :
    displacedRoots (sourcePsiFillDeletedRoot n (s n ψ) (sourceStandardRootMidpoint hp hp1 ψ n)) m =
      sourceStandardRootMidpoint hp hp1 ψ m := by
  obtain ⟨U,_,hψU,_,C,_,hb⟩ := H.offsets ψ hψ
  obtain ⟨α,_,he,_,_⟩ := hb ψ hψU n
  simpa only [hgap,zero_pow (by decide : 2 ≠ 0),zero_mul,add_zero] using he m

/-- The literal root asymptotic at every finite exponent greater than one. -/
theorem sourceLemma12_12 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ : Set (CoeffPair p), IsOpen W₀ ∧ IsConnected W₀ ∧ realTypeSourceLocus p ⊆ W₀ ∧
      ∃ W : Set (CoeffPair p), IsOpen W ∧ IsSimplyConnected W ∧ realTypeSourceLocus p ⊆ W ∧
        ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n, SourceLemma12_12Data hp hp1 W₀ W s := by
  obtain ⟨W₀,ho,hc,hr,W,hW,hs,hrW,s,H⟩ := sourceLemma12_11 hp hp1
  exact ⟨W₀,ho,hc,hr,W,hW,hs,hrW,s,H.lemma12_12 ho⟩

end NLS.ZakharovShabat
