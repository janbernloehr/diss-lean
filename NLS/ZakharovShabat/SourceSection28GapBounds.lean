import NLS.ZakharovShabat.SourceSection27Original
import NLS.ZakharovShabat.SourceLemma28_1
import NLS.ZakharovShabat.SourceLemmaF1
import NLS.ZakharovShabat.NormalizedActionFactorBound

/-! # Section 28's original complex gap and action bounds

One connected L²-open restriction retains the original action family.
The actual deleted product χ has bound 2048, and its gap integral gives
4608 for the original indexed actions, including collapsed complex gaps.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Formula (5.15) for complex sources, including the filled collapsed extension. -/
theorem SourceEquation2_19Data.section28_normalized_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_19Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n : ℤ) (K : ℝ) (hK : 0 ≤ K)
    (hu : ‖sourceActionCriticalCoordinate hp hp1 n ψ‖ ≤ 2)
    (hb : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ n, ‖sourceActionChi hp hp1 n ψ z‖ ≤ K) :
    ‖4*sourceNormalizedIndexedAction hp hp1 n ψ‖ ≤ 9*K := by
  rw [H.normalized_eq_cosineModel ψ hψ n]
  exact norm_normalizedActionCosineModel_le_nine _ _
    (H.previous.chi_cosine_continuous ψ hψ n) K hK
    (fun θ _ => hb _ (sourceActionChi_cosinePoint_mem_gap hp hp1 ψ n θ)) hu

/-- The division-free version of (5.15), valid at every collapsed gap. -/
theorem SourceEquation2_19Data.section28_action_bound
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_19Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W)
    (n : ℤ) (K : ℝ) (hK : 0 ≤ K)
    (hu : ‖sourceActionCriticalCoordinate hp hp1 n ψ‖ ≤ 2)
    (hb : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ n, ‖sourceActionChi hp hp1 n ψ z‖ ≤ K) :
    4*‖sourceIndexedAction hp hp1 n ψ‖ ≤
      9*K*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 := by
  have h := H.section28_normalized_bound ψ hψ n K hK hu hb
  rw [norm_mul,Complex.norm_ofNat] at h
  rw [H.factorization ψ hψ n,norm_mul,norm_pow,sourcePeriodicGapDisplacement_apply]
  nlinarith [mul_le_mul_of_nonneg_right h
    (sq_nonneg ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖)]

/-- The critical coordinate meets the factor-nine hypothesis under Lemma F.1. -/
theorem section28_critical_coordinate_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ)
    (h : ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖ ≤
      ‖canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖) :
    ‖sourceActionCriticalCoordinate hp hp1 n ψ‖ ≤ 2 := by
  unfold sourceActionCriticalCoordinate
  by_cases hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0
  · rw [sourceStandardRootHalfGap,hg,zero_div,div_zero,norm_zero]
    norm_num
  · rw [norm_div,sourceStandardRootHalfGap,norm_div,Complex.norm_ofNat]
    have hpos := norm_pos_iff.mpr hg
    apply (div_le_iff₀ (by positivity)).mpr
    change ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
      canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n‖ ≤ _
    linarith

/-- One open connected restriction implements the F.1 bound before all indices. -/
theorem exists_section28_critical_coordinate_neighborhood
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (hW : IsOpen W) (hreal : realTypeSourceLocus p ⊆ W) :
    ∃ S : Set (CoeffPair p), IsOpen S ∧ IsConnected S ∧ realTypeSourceLocus p ⊆ S ∧ S ⊆ W ∧
      ∀ ψ ∈ S, ∀ n : ℤ, ‖sourceActionCriticalCoordinate hp hp1 n ψ‖ ≤ 2 := by
  classical
  obtain ⟨D⟩ := nonempty_sourceCriticalGapAnalyticDomain hp hp1
  have hl (φ : realTypeSourceSubmodule p) := D.sourceLemmaF1_ii φ.val φ.property
  choose V hV hφV _ hb using hl
  let U := (⋃ φ : realTypeSourceSubmodule p, V φ) ∩ W
  have hU : IsOpen U := (isOpen_iUnion hV).inter hW
  have hrU : realTypeSourceLocus p ⊆ U := fun φ hφ =>
    ⟨mem_iUnion.mpr ⟨⟨φ,hφ⟩,hφV ⟨φ,hφ⟩⟩,hreal hφ⟩
  let S := connectedComponentIn U (0 : CoeffPair p)
  have hs : S ⊆ U := connectedComponentIn_subset U 0
  have hz : (0 : CoeffPair p) ∈ realTypeSourceLocus p := by simp [realTypeSourceLocus]
  refine ⟨S,hU.connectedComponentIn,isConnected_connectedComponentIn_iff.mpr (hrU hz),
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hz hrU,
    fun _ hψ => (hs hψ).2,?_⟩
  intro ψ hψ n
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp (hs hψ).1
  exact section28_critical_coordinate_bound hp hp1 ψ n (hb φ ψ hφ n)

/-- The retained family also carries the original local sequence estimates. -/
theorem SourceSection17OriginalData.section28_originalEstimates
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (D : SourceSection17OriginalData hp hp1 W₀ W V s) : SourceSection11OriginalEstimates hp hp1 W₀ :=
  D.previous.previous.previous.previous.previous.previous.previous.previous.previous.previous

/-- Recover the original gap formulas from the retained map's provenance. -/
theorem SourceSection17OriginalData.section28_gapFormulas
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (D : SourceSection17OriginalData hp hp1 W₀ W V s) : SourceEquation2_19Data hp hp1 W₀ :=
  D.previous.previous.previous.previous.previous.previous.previous.previous.previous.previous.previous

/-- The complex proposition follows directly from the actual χ bound and factor nine. -/
theorem SourceSection27Data.section28_original_chi_neighborhood
    {W₀ W V Wa B U T : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection27Data D A B U T) :
    ∃ S : Set (CoeffPair 2), IsOpen S ∧ IsConnected S ∧ realTypeSourceLocus 2 ⊆ S ∧ S ⊆ T ∧
      S ⊆ sourceSpectralStripNeighborhood (by simp) ∧
      (∀ ψ ∈ S, ∀ n : ℤ, ‖sourceActionCriticalCoordinate (by simp) (by norm_num) n ψ‖ ≤ 2) ∧
      ∀ w : SpectralWeight, w.HasLinearFactor → ∀ a : CoeffPair 2,
        normalizedWeightedSource w a ∈ S → ∀ n : ℤ, 8*‖a‖^2 ≤ 1+|(n:ℝ)| →
          (∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) (normalizedWeightedSource w a) n,
            ‖sourceActionChi (by simp) (by norm_num) n (normalizedWeightedSource w a) z‖ ≤
              2048*(1+‖a‖^2)) ∧
          ‖sourceIndexedAction (by simp) (by norm_num) n (normalizedWeightedSource w a)‖ ≤
            4608*(1+‖a‖^2)*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) (normalizedWeightedSource w a) n‖^2 := by
  let H := D.section28_gapFormulas
  obtain ⟨G,hG,_,hrG,hGs,hg⟩ := exists_sourceM1_gapFactor_neighborhood
  have hR : IsOpen (G ∩ T) := hG.inter Q.gap_open
  have hrR : realTypeSourceLocus 2 ⊆ G ∩ T := fun ψ hψ => ⟨hrG hψ,Q.gap_real_subset hψ⟩
  obtain ⟨S,hS,hconn,hrS,hs,hoff⟩ :=
    exists_section28_critical_coordinate_neighborhood (by simp) (by norm_num) (G ∩ T) hR hrR
  refine ⟨S,hS,hconn,hrS,fun ψ hψ => (hs hψ).2,fun ψ hψ => hGs (hs hψ).1,hoff,?_⟩
  intro w hw a ha n hn
  have haW₀ : normalizedWeightedSource w a ∈ W₀ :=
    D.previous.previous.previous.subset
      (D.complex.source_subset (Q.original_subset (Q.gap_subset (hs ha).2)))
  have hchi : ∀ z ∈ sourcePeriodicSegment (by simp) (by norm_num) (normalizedWeightedSource w a) n,
      ‖sourceActionChi (by simp) (by norm_num) n (normalizedWeightedSource w a) z‖ ≤
        2048*(1+‖a‖^2) := by
    intro z hz
    have h := hg w hw a (hs ha).1 n hn z hz
    rw [sourceCriticalRootRatioExtension_eq_neg_I_chi (by simp) (by norm_num) _ n z
      (H.previous.segment_subset_omitted _ haW₀ n hz)] at h
    simpa only [norm_mul,norm_neg,Complex.norm_I,one_mul] using h
  refine ⟨hchi,?_⟩
  have h := H.section28_action_bound _ haW₀ n (2048*(1+‖a‖^2)) (by positivity)
    (hoff _ ha n) hchi
  nlinarith

end NLS.ZakharovShabat
