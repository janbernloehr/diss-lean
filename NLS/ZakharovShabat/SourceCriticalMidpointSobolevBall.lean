import NLS.ZakharovShabat.SourceHigherSobolevBallCompact
import NLS.ZakharovShabat.SourceCriticalMidpointHigherSobolev

/-! # Uniform critical-midpoint corrections on Sobolev balls

Physical norm comparison, compact quotient bounds and weighted gaps give a complete H^(2s) correction bound on every real Hs ball.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- A native Sobolev ball has a uniform physical Sobolev norm bound. -/
theorem norm_sourcePiSobolevCoordinates_le_native
    (m k : ℕ) (hk : k ≤ m) (a : SobolevSource m) :
    ‖sourcePiSobolevCoordinates m k hk a‖ ≤ 2*(2*Real.pi)^k*‖a‖ := by
  let C := (2*Real.pi)^k
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs (c : ScalarSobolev m) : ‖sourcePiSobolevScalar m k hk c‖ ≤ C*‖c‖ := by
    unfold sourcePiSobolevScalar
    exact WeightedCoeff.norm_weightedMultiplier_le _ _ _ _ hC _ c
  have h1 := (hs a.1).trans (mul_le_mul_of_nonneg_left (norm_fst_le a) hC)
  have h2 := (hs a.2).trans (mul_le_mul_of_nonneg_left (norm_snd_le a) hC)
  have h := norm_withLp_prod_rpow (p := 2) (by simp) (sourcePiSobolevCoordinates m k hk a)
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_two] at h
  change ‖sourcePiSobolevCoordinates m k hk a‖^2 =
    ‖sourcePiSobolevScalar m k hk a.1‖^2+‖sourcePiSobolevScalar m k hk a.2‖^2 at h
  have h1sq := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2sq := pow_le_pow_left₀ (norm_nonneg _) h2 2
  change ‖sourcePiSobolevCoordinates m k hk a‖ ≤ 2*C*‖a‖
  nlinarith [norm_nonneg (sourcePiSobolevCoordinates m k hk a),mul_nonneg hC (norm_nonneg a),sq_nonneg (C*‖a‖)]

/-- Compact real L2 source sets uniformly bound the complete critical
squared-gap quotient, retaining its exact identity at every index. -/
theorem exists_sourceCriticalGapQuotient_bound_on_compact
    (K : Set (CoeffPair 2)) (hK : IsCompact K) (hKreal : K ⊆ realTypeSourceLocus 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ φ ∈ K,
      ‖sourceCriticalGapQuotient (by norm_num) (by norm_num) φ‖ ≤ B ∧ ∀ n : ℤ,
      canonicalCriticalPoints (by norm_num) (by norm_num)
          (periodOnePotential φ) (periodOnePotential_mem _) n-
        canonicalPeriodicMidpoint (by norm_num) (by norm_num)
          (periodOnePotential φ) (periodOnePotential_mem _) n =
        (sourcePeriodicGapDisplacement (by norm_num) (by norm_num) φ n)^2*
          sourceCriticalGapQuotient (by norm_num) (by norm_num) φ n := by
  classical
  have hl (φ : K) := exists_local_uniform_sourceCriticalGapQuotient
    (by norm_num) (by norm_num) φ.val (hKreal φ.property)
  choose U hU hφU B hB hb using hl
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover U hU
    (fun φ hφ => mem_iUnion.mpr ⟨⟨φ,hφ⟩,hφU ⟨φ,hφ⟩⟩)
  refine ⟨∑ φ ∈ S, B φ,Finset.sum_nonneg (fun φ _ => hB φ),?_⟩
  intro φ hφ
  obtain ⟨ψ,hψ⟩ := mem_iUnion.mp (hS hφ)
  obtain ⟨hψS,hφU⟩ := mem_iUnion.mp hψ
  have h := hb ψ φ hφU
  exact ⟨h.1.trans (Finset.single_le_sum (fun φ _ => hB φ) hψS),h.2⟩

/-- The complete critical-midpoint offset is uniformly bounded in H^(2s)
on every real native Hs ball, for all positive integers s. -/
theorem exists_uniform_real_higherSobolev_critical_midpoint_bound
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ab : realTypeHigherSobolevSourceLocus s, ‖ab.val‖ ≤ R →
      ∃ e : ScalarSobolev (2*s),
        (∀ n, e.val n =
          canonicalCriticalPoints (by norm_num) (by norm_num)
            (periodOnePotential (higherSobolevSourceInclusion s ab.val)) (periodOnePotential_mem _) n-
          canonicalPeriodicMidpoint (by norm_num) (by norm_num)
            (periodOnePotential (higherSobolevSourceInclusion s ab.val)) (periodOnePotential_mem _) n) ∧
        ‖e‖ ≤ C := by
  let J := higherSobolevSourceInclusion s
  let X := closedBall (0 : SobolevSource s) R ∩ (J ⁻¹' realTypeSourceLocus 2)
  let K := closure (J '' X)
  obtain ⟨hK,hKreal⟩ := higherSobolev_real_ball_image_compact s hs R
  obtain ⟨B,hB,hquot⟩ := exists_sourceCriticalGapQuotient_bound_on_compact K hK hKreal
  obtain ⟨M,hM,hgap⟩ := exists_sourceHmWeightedGapSequence_bound_on_physical_ball s hs
    (2*(2*Real.pi)^s*R)
  refine ⟨M^2*B,by positivity,?_⟩
  intro ab hab
  have hmem : J ab.val ∈ K := subset_closure ⟨ab.val,
    ⟨by simpa only [mem_closedBall,dist_zero_right] using hab,ab.property⟩,rfl⟩
  have hgap' : ‖sourceHmWeightedGapSequence s ab.val‖ ≤ M := hgap ab
    ((norm_sourcePiSobolevCoordinates_le_native s s le_rfl ab.val).trans (by gcongr))
  let g := sourcePeriodicGapDisplacement (by norm_num) (by norm_num) (J ab.val)
  let q := sourceCriticalGapQuotient (by norm_num) (by norm_num) (J ab.val)
  have hg (n : ℤ) : (1+|(n:ℝ)|)^s*‖g n‖ ≤ M :=
    (sourceHmWeightedGapSequence_majorant s ab.val n).trans
      ((lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) _ n).trans hgap')
  obtain ⟨e,he,hen⟩ := WeightedCoeff.exists_sobolev_square_mul s (fun n => g n) q M hg
  refine ⟨e,?_,hen.trans (mul_le_mul_of_nonneg_left (hquot (J ab.val) hmem).1 (sq_nonneg M))⟩
  intro n
  rw [he]
  exact ((hquot (J ab.val) hmem).2 n).symm

end NLS.ZakharovShabat
