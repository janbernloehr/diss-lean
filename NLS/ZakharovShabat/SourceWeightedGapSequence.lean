import NLS.ZakharovShabat.SourceBirkhoffWeightedMembership
import NLS.ZakharovShabat.SourceWeightedGapAsymptotics

/-! # Locally uniform bounds for actual weighted gap sequences

Compatible complex source maps produce the full weighted gap sequence.
On a common complex neighborhood its lp norm is bounded and every sufficiently
large finite truncation has a uniformly small tail. No real-type assumption
or continuous choice of the ordered gap endpoints is used.
-/
noncomputable section
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The full actual weighted gap sequence for compatible original and weighted source maps. -/
def sourceWeightedGapSequence (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (L : E →L[ℂ] CoeffPair p) (S : E →L[ℂ] WeightedCoeffPair w.toWeight p)
    (hSL : ∀ a, weightedBaseToPair w (S a) = periodOnePotential (L a)) (a : E) : Coeff p :=
  ⟨fun n => (w (2*n) : ℂ) * sourcePeriodicGapDisplacement hp hp1 (L a) n,
    sourceWeightedGap_mem hp hp1 w (L a) (S a) (hSL a)⟩

@[simp] theorem sourceWeightedGapSequence_apply (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (L : E →L[ℂ] CoeffPair p) (S : E →L[ℂ] WeightedCoeffPair w.toWeight p)
    (hSL : ∀ a, weightedBaseToPair w (S a) = periodOnePotential (L a)) (a : E) (n : ℤ) :
    sourceWeightedGapSequence hp hp1 w L S hSL a n =
      (w (2*n) : ℂ) * sourcePeriodicGapDisplacement hp hp1 (L a) n := rfl

/-- One complex weighted neighborhood bounds the norm of every actual weighted gap sequence. -/
theorem exists_local_sourceWeightedGapSequence_bound (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (L : E →L[ℂ] CoeffPair p)
    (S : E →L[ℂ] WeightedCoeffPair w.toWeight p)
    (hSL : ∀ b, weightedBaseToPair w (S b) = periodOnePotential (L b)) (a : E) :
    ∃ U : Set E, IsOpen U ∧ a ∈ U ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ b ∈ U, ‖sourceWeightedGapSequence hp hp1 w L S hSL b‖ ≤ C := by
  classical
  have hp0 := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  obtain ⟨N, _, V, hV, haV, htail⟩ :=
    exists_uniform_canonicalWeightedGapSummability hp hp1 w (S a)
  obtain ⟨M, _, T, hT, _, haT, _, hbudget⟩ :=
    exists_uniform_small_rootGapBudget hp hp1 w (S a) (by norm_num : (0 : ℝ) < 1)
  obtain ⟨_, _, W, hW, haW, R, hR, hgap⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 (L a) (by norm_num : (0 : ℝ) < 1)
  let K := max N M
  let U := S ⁻¹' (V ∩ T) ∩ L ⁻¹' W
  let s := Finset.Icc (-(K : ℤ)) K
  let H := fun n : ℤ => if n ∈ s then (w (2*n))^p.toReal * R^p.toReal else 0
  have hHs : Summable H := summable_of_ne_finset_zero (s := s) (by intro n hn; simp [H, hn])
  have hHn (n : ℤ) : 0 ≤ H n := by
    dsimp [H]
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (w.toWeight.positive _).le _) (Real.rpow_nonneg hR _)
    · exact le_rfl
  have hB : 0 ≤ (∑' n, H n) + 1 := add_nonneg (tsum_nonneg hHn) zero_le_one
  refine ⟨U, ((hV.inter hT).preimage S.continuous).inter (hW.preimage L.continuous),
    ⟨⟨haV, haT⟩, haW⟩, ((∑' n, H n)+1) ^ p.toReal⁻¹, Real.rpow_nonneg hB _, ?_⟩
  intro b hb
  have heven : weightedBaseToPair w (S b) ∈ pairParitySubspace 0 := by
    rw [hSL b]; exact periodOnePotential_mem _
  obtain ⟨hqs, hqb⟩ := htail (S b) hb.1.1 heven K (le_max_left _ _)
  let g := sourceWeightedGapSequence hp hp1 w L S hSL b
  let Q := fun n : ℤ => if K ≤ n.natAbs then ‖g n‖^p.toReal else 0
  have hQs : Summable Q := by
    simpa only [Q, g, sourceWeightedGapSequence_apply, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (w.toWeight.positive _),
      Real.mul_rpow (w.toWeight.positive _).le (norm_nonneg _),
      hSL b, sourcePeriodicGapDisplacement_apply] using hqs
  have hQb : (∑' n, Q n) ≤ 1 := by
    have h := hqb.trans (hbudget (S b) hb.1.2 K (le_max_right _ _)).le
    simpa only [Q, g, sourceWeightedGapSequence_apply, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (w.toWeight.positive _),
      Real.mul_rpow (w.toWeight.positive _).le (norm_nonneg _),
      hSL b, sourcePeriodicGapDisplacement_apply] using h
  have hpoint (n : ℤ) : ‖g n‖^p.toReal ≤ H n + Q n := by
    by_cases hn : K ≤ n.natAbs
    · simp only [Q, if_pos hn]
      exact le_add_of_nonneg_left (hHn n)
    · have hns : n ∈ s := by simp only [s, Finset.mem_Icc]; omega
      simp only [Q, if_neg hn, H, if_pos hns, add_zero]
      change ‖(w (2*n) : ℂ) * sourcePeriodicGapDisplacement hp hp1 (L b) n‖^p.toReal ≤ _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (w.toWeight.positive _),
        Real.mul_rpow (w.toWeight.positive _).le (norm_nonneg _)]
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (w.toWeight.positive _).le _)
      exact Real.rpow_le_rpow (norm_nonneg _)
        ((lp.norm_apply_le_norm (zero_lt_one.trans hp1).ne' _ n).trans (hgap (L b) hb.2).1)
        ENNReal.toReal_nonneg
  apply (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) hB hp0).mpr
  change ‖g‖^p.toReal ≤ _
  rw [lp.norm_rpow_eq_tsum hp0]
  exact ((g.property.summable hp0).tsum_le_tsum hpoint (hHs.add hQs)).trans
    (by rw [hHs.tsum_add hQs]; exact add_le_add le_rfl hQb)

end NLS.ZakharovShabat

namespace NLS.ZakharovShabat
open Set Filter Topology
open scoped ENNReal
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- On one weighted complex neighborhood, all later truncations have uniformly small gap tails. -/
theorem exists_uniform_small_sourceWeightedGapSequence (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (L : E →L[ℂ] CoeffPair p)
    (S : E →L[ℂ] WeightedCoeffPair w.toWeight p)
    (hSL : ∀ b, weightedBaseToPair w (S b) = periodOnePotential (L b))
    (a : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∃ U : Set E, IsOpen U ∧ a ∈ U ∧ ∀ b ∈ U, ∀ M : ℕ, N ≤ M →
      ‖sourceWeightedGapSequence hp hp1 w L S hSL b -
        Coeff.truncate (Finset.Icc (-(M : ℤ)) M) (sourceWeightedGapSequence hp hp1 w L S hSL b)‖ ≤ ε := by
  classical
  have hp0 := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  obtain ⟨N, _, V, hV, haV, htail⟩ :=
    exists_uniform_canonicalWeightedGapSummability hp hp1 w (S a)
  obtain ⟨M, _, T, hT, _, haT, _, hbudget⟩ :=
    exists_uniform_small_rootGapBudget hp hp1 w (S a) (Real.rpow_pos_of_pos hε p.toReal)
  refine ⟨max N M, S ⁻¹' (V ∩ T), (hV.inter hT).preimage S.continuous, ⟨haV, haT⟩, ?_⟩
  intro b hb K hK
  have heven : weightedBaseToPair w (S b) ∈ pairParitySubspace 0 := by
    rw [hSL b]; exact periodOnePotential_mem _
  have hnK : N ≤ K+1 := by omega
  have hmK : M ≤ K+1 := by omega
  obtain ⟨_, hqb⟩ := htail (S b) hb.1 heven (K+1) hnK
  have hbound := hqb.trans (hbudget (S b) hb.2 (K+1) hmK).le
  let g := sourceWeightedGapSequence hp hp1 w L S hSL b
  let ss := Finset.Icc (-(K : ℤ)) K
  have heq : (fun n : ℤ => ‖(g - Coeff.truncate ss g) n‖ ^ p.toReal) =
      (fun n : ℤ => if K+1 ≤ n.natAbs then (w (2*n))^p.toReal *
        ‖canonicalPeriodicGap hp hp1 (weightedBaseToPair w (S b)) heven n‖^p.toReal else 0) := by
    funext n
    by_cases hn : K+1 ≤ n.natAbs
    · have hns : n ∉ ss := by simp only [ss, Finset.mem_Icc]; omega
      simp only [lp.coeFn_sub, Pi.sub_apply, Coeff.truncate_apply, if_neg hns, sub_zero, if_pos hn,
        g, sourceWeightedGapSequence_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (w.toWeight.positive _), Real.mul_rpow (w.toWeight.positive _).le (norm_nonneg _),
        hSL b, sourcePeriodicGapDisplacement_apply]
    · have hns : n ∈ ss := by simp only [ss, Finset.mem_Icc]; omega
      simp only [lp.coeFn_sub, Pi.sub_apply, Coeff.truncate_apply, if_pos hns, sub_self, if_neg hn,
        norm_zero, Real.zero_rpow hp0.ne']
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) hε.le hp0).mp
  change ‖g-Coeff.truncate ss g‖^p.toReal ≤ _
  rw [lp.norm_rpow_eq_tsum hp0, heq]
  exact hbound

end NLS.ZakharovShabat
