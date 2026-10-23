import NLS.ZakharovShabat.SourcePeriodTwoCanonicalMidpointGap
import NLS.ZakharovShabat.SourceCeilingCutoffEstimates
import NLS.ZakharovShabat.SourcePositiveGapTail

/-! # Weighted power tails of the complete canonical period-two gaps

The actual canonical pairs are compared with the intrinsic contour gaps
past one common cutoff. This transfers corrected weighted estimates and
local smallness to the canonical sequence without imposing even support.
-/
noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private theorem canonicalWeightedUniformPullback (w : SpectralWeight)
    (e : WeightedCoeffPair w.toWeight p →L[ℂ] CoeffPair p)
    (φ : WeightedCoeffPair w.toWeight p) (P : ℕ → CoeffPair p → Prop)
    (h : ∃ N : ℕ, 2 ≤ N ∧ ∃ V : Set (CoeffPair p),
      IsOpen V ∧ Convex ℝ V ∧ e φ ∈ V ∧ 0 ∈ V ∧ ∀ ψ ∈ V, P N ψ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, P N (e ψ) := by
  obtain ⟨N,hN,V,ho,hc,hφ,h0,hr⟩ := h
  exact ⟨N,hN,e ⁻¹' V,ho.preimage e.continuous,
    hc.linear_preimage (e.restrictScalars ℝ).toLinearMap,hφ,
    by simpa only [Set.mem_preimage,map_zero] using h0,fun ψ hψ => hr (e ψ) hψ⟩

/-- On one weighted-input neighborhood, the fixed canonical labels give both intrinsic gap tails. -/
theorem sourceCanonicalWeightedGapTails_eq (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∀ K : ℕ, N₀ < K →
        let ξ := sourcePeriodTwoCanonicalLeft hp hp1 (sourceWeightedPeriodTwoInput w ψ)
        let η := sourcePeriodTwoCanonicalRight hp hp1 (sourceWeightedPeriodTwoInput w ψ)
        periodicGapPowerTail hp w ψ K = rootGapPowerTail p w K ξ η ∧
          sourcePositiveGapPowerTail hp w ψ K = sourcePositiveRootGapPowerTail p w K ξ η := by
  obtain ⟨N,hN,U,ho,hc,hφ,h0,hr⟩ := canonicalWeightedUniformPullback w
    (sourceWeightedPeriodTwoInput w) φ _
    (sourcePeriodTwoCanonicalMidpointGap_eq_contours hp hp1 (sourceWeightedPeriodTwoInput w φ))
  refine ⟨N,hN,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ K hK
  have hg (n : ℤ) (hn : K ≤ n.natAbs) :
      periodicSquaredGap hp (weightedBaseToPair w ψ) n =
        (sourcePeriodTwoCanonicalLeft hp hp1 (sourceWeightedPeriodTwoInput w ψ) n-
          sourcePeriodTwoCanonicalRight hp hp1 (sourceWeightedPeriodTwoInput w ψ) n)^2 := by
    have h := (hr ψ hψ n (by omega)).2
    rw [toMax_sourceWeightedPeriodTwoInput] at h
    calc
      _ = sourcePeriodTwoCanonicalGap hp hp1 (sourceWeightedPeriodTwoInput w ψ) n ^ 2 := h.symm
      _ = _ := by unfold sourcePeriodTwoCanonicalGap; ring
  exact ⟨periodicGapPowerTail_eq_rootGapPowerTail hp w ψ K _ _ hg,
    sourcePositiveGapPowerTail_eq_rootGap hp w ψ K _ _ (fun n hn => hg n (by omega))⟩

/-- The fixed canonical weighted gaps satisfy full-cutoff bounds and locally small signed tails. -/
theorem sourceProposition6_3_canonical_signed (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∀ K : ℕ, N₀ < K →
        let ξ := sourcePeriodTwoCanonicalLeft hp hp1 (sourceWeightedPeriodTwoInput w ψ)
        let η := sourcePeriodTwoCanonicalRight hp hp1 (sourceWeightedPeriodTwoInput w ψ)
        Summable (rootGapPowerTail p w K ξ η) ∧
          (∑' n : ℤ, rootGapPowerTail p w K ξ η n) ≤ rootGapBudget_fullCutoff w ψ K ∧
          (∑' n : ℤ, rootGapPowerTail p w K ξ η n) ≤ rootGapBudget_ceilingHalf w ψ K ∧
          (∑' n : ℤ, rootGapPowerTail p w K ξ η n) < ε := by
  obtain ⟨Ne,hNe,V,hoV,hcV,hφV,h0V,he⟩ := sourceCanonicalWeightedGapTails_eq hp hp1 w φ
  obtain ⟨Nb,_,W,hoW,hcW,hφW,h0W,hb⟩ := sourceProposition6_3_corrected_fullCutoff hp hp1 w φ
  obtain ⟨Ns,_,S,hoS,hcS,hφS,h0S,hs⟩ := sourceProposition6_3_small_tails hp hp1 w φ hε
  refine ⟨max Ne (max Nb Ns),hNe.trans (le_max_left _ _),V ∩ (W ∩ S),
    hoV.inter (hoW.inter hoS),hcV.inter (hcW.inter hcS),⟨hφV,hφW,hφS⟩,⟨h0V,h0W,h0S⟩,?_⟩
  intro ψ hψ K hK
  dsimp only
  rw [← (he ψ hψ.1 K (by omega)).1]
  obtain ⟨_,_,_,_,ht⟩ := hb ψ hψ.2.1
  have hbound := (ht K (by omega)).2
  exact ⟨(ht K (by omega)).1,hbound,
    hbound.trans (rootGapBudget_fullCutoff_le_ceilingHalf hp w ψ K),(hs ψ hψ.2.2 K (by omega)).2⟩

/-- The same fixed canonical gaps obey the exact printed positive-index range with corrected budgets. -/
theorem sourceProposition6_3_canonical_positive (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∀ K : ℕ, N₀ < K →
        let ξ := sourcePeriodTwoCanonicalLeft hp hp1 (sourceWeightedPeriodTwoInput w ψ)
        let η := sourcePeriodTwoCanonicalRight hp hp1 (sourceWeightedPeriodTwoInput w ψ)
        Summable (sourcePositiveRootGapPowerTail p w K ξ η) ∧
          (∑' n : ℤ, sourcePositiveRootGapPowerTail p w K ξ η n) ≤ rootGapBudget_fullCutoff w ψ K ∧
          (∑' n : ℤ, sourcePositiveRootGapPowerTail p w K ξ η n) ≤ rootGapBudget_ceilingHalf w ψ K ∧
          (∑' n : ℤ, sourcePositiveRootGapPowerTail p w K ξ η n) < ε := by
  obtain ⟨Ne,hNe,V,hoV,hcV,hφV,h0V,he⟩ := sourceCanonicalWeightedGapTails_eq hp hp1 w φ
  obtain ⟨Nb,_,W,hoW,hcW,hφW,h0W,hb⟩ := sourceProposition6_3_canonical_signed hp hp1 w φ hε
  refine ⟨max Ne Nb,hNe.trans (le_max_left _ _),V ∩ W,hoV.inter hoW,hcV.inter hcW,
    ⟨hφV,hφW⟩,⟨h0V,h0W⟩,?_⟩
  intro ψ hψ K hK
  obtain ⟨heS,heP⟩ := he ψ hψ.1 K (by omega)
  have hr := hb ψ hψ.2 K (by omega)
  dsimp only at hr ⊢
  rw [← heS] at hr
  rw [← heP]
  have hle := tsum_sourcePositiveGapPowerTail_le hp w ψ K hr.1
  exact ⟨summable_sourcePositiveGapPowerTail hp w ψ K hr.1,hle.trans hr.2.1,
    hle.trans hr.2.2.1,hle.trans_lt hr.2.2.2⟩

/-- The actual complete canonical gap has the weighted ℓᵖ regularity asserted in Proposition 6.3. -/
theorem sourceProposition6_3_canonical_gap_mem (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    Memℓp (fun n : ℤ => (w (2*n) : ℂ) *
      sourcePeriodTwoCanonicalGap hp hp1 (sourceWeightedPeriodTwoInput w φ) n) p := by
  obtain ⟨N,_,U,_,_,hφ,_,ht⟩ := sourceProposition6_3_canonical_signed hp hp1 w φ (by norm_num : (0 : ℝ) < 1)
  let F (n : ℤ) := (w (2*n)*‖sourcePeriodTwoCanonicalGap hp hp1 (sourceWeightedPeriodTwoInput w φ) n‖)^p.toReal
  have hf : (fun n : ℤ => if N+1 ≤ n.natAbs then (0 : ℝ) else F n).HasFiniteSupport := by
    apply (Set.finite_Icc (-(N+1 : ℕ) : ℤ) (N+1 : ℕ)).subset
    intro n hn
    have h : ¬N+1 ≤ n.natAbs := by
      intro h
      exact hn (if_pos h)
    constructor <;> omega
  have hs : Summable F := by
    convert (ht φ hφ (N+1) (by omega)).1.add (summable_of_hasFiniteSupport hf) using 1
    funext n
    simp only [rootGapPowerTail,F,sourcePeriodTwoCanonicalGap,norm_sub_rev]
    split_ifs <;> simp
  apply (memℓp_gen_iff (ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp)).mpr
  convert hs using 1
  funext n
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (zero_le_one.trans (w.one_le _))]

end NLS.ZakharovShabat
