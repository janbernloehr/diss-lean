import NLS.ZakharovShabat.SourceProfileActionUpperBound
import NLS.ZakharovShabat.SourceSobolevOpenGapDensity
import NLS.ZakharovShabat.SourceSobolevFiniteGapDensity
import NLS.ZakharovShabat.SourceNormalizedActionLowerBound

/-! # Uniform H1 decay of the actual normalized action and root

The exact normalized-action error and root error decay as (1+|n|)^(-2),
uniformly on physical H1 balls. Density is applied to open-gap finite-gap
sources in H1 itself, then continuity includes all collapsed gaps.
These estimates are real-source bounds; stronger-target analyticity is
not asserted.
-/

noncomputable section
open Set Metric Complex MeasureTheory
open scoped ENNReal

namespace NLS.ZakharovShabat

/-- Physical Sobolev scalar coordinates are continuous at every retained integer order. -/
theorem continuous_sourcePiSobolevScalar (m k : ℕ) (hk : k ≤ m) :
    Continuous (sourcePiSobolevScalar m k hk) := by
  unfold sourcePiSobolevScalar
  generalize_proofs
  exact (WeightedCoeff.weightIsometry _ 2).continuous.comp
    (WeightedCoeff.weightedMultiplierCLM _ _ _ ((2*Real.pi)^k) (by positivity) (by assumption)).continuous

/-- The exact physical H1 coordinate map is continuous. -/
theorem continuous_sourcePhysicalH1Coordinates : Continuous sourcePhysicalH1Coordinates := by
  have hs := continuous_sourcePiSobolevScalar 1 1 le_rfl
  have hp : Continuous (sourcePiSobolevCoordinates 1 1 le_rfl) :=
    (CoeffPair.toMax 2).symm.continuous.comp ((hs.comp continuous_fst).prodMk (hs.comp continuous_snd))
  exact hp.comp higherSobolevSourceOneEquiv.continuous

/-- A finite-gap action upper bound on an open H1 set controls the normalized action even at collapsed gaps. -/
theorem sourceNormalizedAction_upper_of_finiteGap_on_open_H1
    (U : Set realTypeSobolevSourceLocus) (hU : IsOpen U) (n : ℤ) (E : ℝ)
    (hf : ∀ a ∈ U, a ∈ sourceSobolevFiniteGapLocus →
      4*‖sourceComplexAction (by simp) (by norm_num) n (sobolevSourceInclusion a.val)‖ ≤
        ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion a.val) n‖^2*(1+E))
    (a : realTypeSobolevSourceLocus) (ha : a ∈ U) :
    4*(sourceNormalizedActionComplexExtension (by simp) (by norm_num) n (sobolevSourceInclusion a.val)).re-1 ≤ E := by
  have hL : Continuous (fun a : realTypeSobolevSourceLocus => sobolevSourceInclusion a.val) :=
    sobolevSourceInclusion.continuous.comp continuous_subtype_val
  have hS : Continuous sourceH1RealSource := hL.subtype_mk (fun a => a.property)
  have hOpen : IsOpen (sourceSobolevOpenGapRealLocus n) :=
    (isOpen_sourceOpenGapRealLocus (by simp) (by norm_num) n).preimage hS
  have hDense := (dense_sourceSobolevOpenGapRealLocus n).inter_of_isOpen_left
    dense_sourceSobolevFiniteGapLocus hOpen
  have hρ : Continuous (fun b : realTypeSobolevSourceLocus =>
      (sourceNormalizedActionComplexExtension (by simp) (by norm_num) n (sobolevSourceInclusion b.val)).re) := by
    apply continuous_iff_continuousAt.mpr
    intro b
    have hbase := (differentiableAt_sourceNormalizedActionComplexExtension_of_realType (by simp) (by norm_num)
      (sobolevSourceInclusion b.val) b.property n).continuousAt
    have hcomp := hbase.comp (f := fun a : realTypeSobolevSourceLocus => sobolevSourceInclusion a.val)
      (x := b) (hL.continuousAt (x := b))
    simpa only [Function.comp_def] using! Complex.continuous_re.continuousAt.comp hcomp
  have hcρ : IsClosed {b : realTypeSobolevSourceLocus |
      4*(sourceNormalizedActionComplexExtension (by simp) (by norm_num) n (sobolevSourceInclusion b.val)).re-1 ≤ E} :=
    isClosed_le ((continuous_const.mul hρ).sub continuous_const) continuous_const
  have hsubρ : U ∩ (sourceSobolevOpenGapRealLocus n ∩ sourceSobolevFiniteGapLocus) ⊆ {b : realTypeSobolevSourceLocus |
      4*(sourceNormalizedActionComplexExtension (by simp) (by norm_num) n (sobolevSourceInclusion b.val)).re-1 ≤ E} := by
    intro b hb
    have hg : sourcePeriodicGapDisplacement (by simp) (by norm_num) (sobolevSourceInclusion b.val) n ≠ 0 := by
      simpa only [sourcePeriodicGapDisplacement_apply,sourceSobolevOpenGapRealLocus,Set.mem_ofPred_eq] using hb.2.1
    obtain ⟨T,_,hbT,_,hfactor⟩ := exists_local_sourceNormalizedActionComplexExtension_differentiableOn
      (by simp) (by norm_num) (sobolevSourceInclusion b.val) b.property n
    let ρ := sourceNormalizedActionComplexExtension (by simp) (by norm_num) n (sobolevSourceInclusion b.val)
    have hi : ρ.im = 0 := sourceNormalizedActionComplexExtension_im_eq_zero_of_realType (by simp) (by norm_num)
      n (sobolevSourceInclusion b.val) b.property
    have hpρ : 0 ≤ ρ.re := (sourceNormalizedActionComplexExtension_re_pos_of_realType (by simp) (by norm_num)
      n (sobolevSourceInclusion b.val) b.property).le
    have he : ρ = (ρ.re:ℂ) := Complex.ext rfl (by simpa only [Complex.ofReal_im] using hi)
    have hn : ‖ρ‖ = ρ.re := by rw [he,Complex.norm_real,Real.norm_of_nonneg hpρ]; rfl
    have h := hf b hb.1 hb.2.2
    rw [hfactor _ hbT,norm_mul,norm_pow] at h
    change 4*(_*‖ρ‖) ≤ _ at h
    rw [hn] at h
    have hpos := pow_pos (norm_pos_iff.mpr hg) 2
    change 4*ρ.re-1 ≤ E
    nlinarith
  exact closure_minimal hsubρ hcρ (hDense.open_subset_closure_inter hU ha)

/-- The exact normalized-action error decays quadratically in the index, uniformly on physical H1 balls. -/
theorem sourceNormalizedAction_uniform_physical_H1_decay (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : realTypeSobolevSourceLocus, ‖sourcePhysicalH1Coordinates a.val‖ ≤ R →
      ∀ n : ℤ, (1+|(n:ℝ)|)^2*‖4*sourceNormalizedActionComplexExtension (by simp) (by norm_num) n
        (sobolevSourceInclusion a.val)-1‖ ≤ K := by
  obtain ⟨K,hK,hbound⟩ := sourceExteriorGapCorrection_uniform_physical_H1_ball (R+1)
  obtain ⟨W,_,_,⟨A⟩⟩ := exists_sourcePrimitivePowerAtlas (by simp : (2:ℝ≥0∞) ≠ ⊤) (by norm_num)
  let U : Set realTypeSobolevSourceLocus := {b | ‖sourcePhysicalH1Coordinates b.val‖ < R+1}
  have hU : IsOpen U := isOpen_lt
    (continuous_sourcePhysicalH1Coordinates.comp continuous_subtype_val).norm continuous_const
  refine ⟨K,hK,?_⟩
  intro a ha n
  have haU : a ∈ U := by change _ < R+1; linarith
  have hup := sourceNormalizedAction_upper_of_finiteGap_on_open_H1 U hU n (K/(1+|(n:ℝ)|)^2) (fun b hb hf => ?_) a haU
  · let ρ := sourceNormalizedActionComplexExtension (by simp) (by norm_num) n (sobolevSourceInclusion a.val)
    have hi : ρ.im = 0 := sourceNormalizedActionComplexExtension_im_eq_zero_of_realType (by simp) (by norm_num)
      n (sobolevSourceInclusion a.val) a.property
    have he : ρ = (ρ.re:ℂ) := Complex.ext rfl (by simpa only [Complex.ofReal_im] using hi)
    have hlo : (1/4:ℝ) ≤ ρ.re := sourceNormalizedActionComplexExtension_re_ge_quarter (by simp) (by norm_num) (sourceH1RealSource a) n
    have hn : ‖4*ρ-1‖ = 4*ρ.re-1 := by
      rw [he]
      have hcast : (4:ℂ)*(ρ.re:ℂ)-1 = ((4*ρ.re-1:ℝ):ℂ) := by push_cast; rfl
      rw [hcast,Complex.norm_real,Real.norm_of_nonneg (by linarith : 0 ≤ 4*ρ.re-1)]
      rfl
    change (1+|(n:ℝ)|)^2*‖4*ρ-1‖ ≤ K
    rw [hn]
    have h := (le_div_iff₀ (by positivity : 0 < (1+|(n:ℝ)|)^2)).mp hup
    nlinarith
  · apply A.real_action_le_gap_sq_of_exteriorCorrection_bound_finiteGap (sourceH1RealSource b) n hf
    intro hg θ _
    have h := hbound b (le_of_lt hb) n hg θ
    exact (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using h)

/-- The actual normalized-root error inherits quadratic decay, including collapsed gaps. -/
theorem sourceNormalizedActionRoot_uniform_physical_H1_decay (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a : realTypeSobolevSourceLocus, ‖sourcePhysicalH1Coordinates a.val‖ ≤ R →
      ∀ n : ℤ, (1+|(n:ℝ)|)^2*‖sourceNormalizedActionRoot (by simp) (by norm_num) n
        (sobolevSourceInclusion a.val)-1‖ ≤ K := by
  obtain ⟨K,hK,h⟩ := sourceNormalizedAction_uniform_physical_H1_decay R
  refine ⟨K/2,by positivity,?_⟩
  intro a ha n
  have hr := sourceNormalizedActionRoot_deviation_le_half (by simp) (by norm_num) (sourceH1RealSource a) n
  dsimp only [sourceH1RealSource] at hr
  have hm := mul_le_mul_of_nonneg_left hr (sq_nonneg (1+|(n:ℝ)|))
  nlinarith [h a ha n]

end NLS.ZakharovShabat
