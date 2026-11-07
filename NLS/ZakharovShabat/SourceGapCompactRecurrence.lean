import NLS.FunctionalAnalysis.CompactThreshold
import NLS.ZakharovShabat.SourceGapWeightedTail

/-!
# A common forced Fourier-tail recurrence on compact source families

The original real source and its weighted realization may vary continuously
on any compact parameter space. One cutoff then works for every parameter,
every larger cutoff and both signed Fourier tails. The actual gap forcing
and the full original weighted norm budget are retained.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Actual center-gap bounds have a common cutoff on a compact family of
real sources and compatible weighted realizations. -/
theorem exists_compact_weightedResonantCenter_gap_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (φ : T → realTypeSourceSubmodule p) (ψ : T → WeightedCoeffPair w.toWeight p)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hrel : ∀ t, w.forgetPairWeight (ψ t) = sourceWeightedPeriodOne (φ t).val) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ t, ∀ n : ℤ, N ≤ n.natAbs →
      let ζ := weightedResonantDiagonalCenter hp w (ψ t) n
      ‖weightedResonantBPlusExtension hp w (ψ t) n ζ‖ ≤
        2*‖sourcePeriodicGapDisplacement hp hp1 (φ t).val n‖ ∧
      ‖weightedResonantBMinusExtension hp w (ψ t) n ζ‖ ≤
        2*‖sourcePeriodicGapDisplacement hp hp1 (φ t).val n‖ := by
  let P := fun t N => ∀ n : ℤ, N ≤ n.natAbs →
    let ζ := weightedResonantDiagonalCenter hp w (ψ t) n
    ‖weightedResonantBPlusExtension hp w (ψ t) n ζ‖ ≤
      2*‖sourcePeriodicGapDisplacement hp hp1 (φ t).val n‖ ∧
    ‖weightedResonantBMinusExtension hp w (ψ t) n ζ‖ ≤
      2*‖sourcePeriodicGapDisplacement hp hp1 (φ t).val n‖
  have hlocal : ∀ t, ∃ N : ℕ, ∃ U : Set T, IsOpen U ∧ t ∈ U ∧
      ∀ s ∈ U, ∀ M : ℕ, N ≤ M → P s M := by
    intro t
    obtain ⟨N₁,_,U₁,ho₁,ht₁,hforget⟩ := exists_uniform_weightedResonantCenter_forget hp hp1 w (ψ t)
    obtain ⟨N₂,_,U₂,ho₂,ht₂,hgap⟩ := exists_uniform_sourceResonantCenter_gap_bound hp hp1 (φ t).val
    refine ⟨max N₁ N₂,ψ ⁻¹' U₁ ∩ (fun s => (φ s).val) ⁻¹' U₂,
      (ho₁.preimage hψ).inter (ho₂.preimage (continuous_subtype_val.comp hφ)),⟨ht₁,ht₂⟩,?_⟩
    intro s hs M hM n hn
    have hf := hforget (ψ s) hs.1 n (by omega)
    rw [hrel s] at hf
    dsimp only
    rw [hf.2.1,hf.2.2]
    exact hgap (φ s).val hs.2 (φ s).property n (by omega)
  obtain ⟨N,hN⟩ := exists_uniform_nat_threshold_on_compact P hlocal
  exact ⟨max 2 N,le_max_left _ _,fun t => hN t (max 2 N) (le_max_right _ _)⟩

/-- The original remainder membership and budget hold beyond one common
cutoff for every member of a compact weighted family. -/
theorem exists_compact_weightedResonantCenterRemainder_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (ψ : T → WeightedCoeffPair w.toWeight p) (hψ : Continuous ψ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ t, ∀ N : ℕ, N₀ ≤ N →
      (∀ positive : Bool, Memℓp (weightedResonantCenterRemainderCoordinate hp w (ψ t) N positive) p) ∧
      ‖weightedResonantCenterRemainder hp w (ψ t) N‖^p.toReal ≤
        offDiagonalSummationConstant p * ‖ψ t‖^p.toReal *
          (‖ψ t‖^(2*p.toReal)/(N:ℝ)^(min 1 (p.toReal-1)) +
            ‖weightedPairFourierTail w.toWeight (N/2) (ψ t)‖^(2*p.toReal)) := by
  let P := fun t N =>
    (∀ positive : Bool, Memℓp (weightedResonantCenterRemainderCoordinate hp w (ψ t) N positive) p) ∧
    ‖weightedResonantCenterRemainder hp w (ψ t) N‖^p.toReal ≤
      offDiagonalSummationConstant p * ‖ψ t‖^p.toReal *
        (‖ψ t‖^(2*p.toReal)/(N:ℝ)^(min 1 (p.toReal-1)) +
          ‖weightedPairFourierTail w.toWeight (N/2) (ψ t)‖^(2*p.toReal))
  have hlocal : ∀ t, ∃ N : ℕ, ∃ U : Set T, IsOpen U ∧ t ∈ U ∧
      ∀ s ∈ U, ∀ M : ℕ, N ≤ M → P s M := by
    intro t
    obtain ⟨N,_,U,ho,_,ht,_,hb⟩ := exists_uniform_weightedResonantCenterRemainder_bound hp hp1 w (ψ t)
    exact ⟨N,ψ ⁻¹' U,ho.preimage hψ,ht,fun s hs M hM => hb (ψ s) hs M hM⟩
  obtain ⟨N,hN⟩ := exists_uniform_nat_threshold_on_compact P hlocal
  exact ⟨max 2 N,le_max_left _ _,fun t M hM => hN t M ((le_max_right _ _).trans hM)⟩

/-- A coordinate center-gap bound and proved remainder membership give the
actual closing-tail budget at that cutoff, with no asymptotic hypothesis. -/
theorem weightedResonantCenterClosingTail_le_of_gap_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p)
    (w : SpectralWeight) (ψ : WeightedCoeffPair w.toWeight p)
    (hψ : w.forgetPairWeight ψ = sourceWeightedPeriodOne φ.val) (M : ℕ)
    (hmem : ∀ positive : Bool, Memℓp (weightedResonantCenterRemainderCoordinate hp w ψ M positive) p)
    (hgap : ∀ n : ℤ, M ≤ n.natAbs →
      let ζ := weightedResonantDiagonalCenter hp w ψ n
      ‖weightedResonantBPlusExtension hp w ψ n ζ‖ ≤ 2*‖sourcePeriodicGapDisplacement hp hp1 φ.val n‖ ∧
      ‖weightedResonantBMinusExtension hp w ψ n ζ‖ ≤ 2*‖sourcePeriodicGapDisplacement hp hp1 φ.val n‖) :
    ‖weightedResonantCenterClosingTail hp w ψ M‖^p.toReal ≤
      (2*(2:ℝ)^p.toReal)*sourceWeightedGapPowerTail hp hp1 w φ.val M := by
  have hp0 := ENNReal.toReal_pos (zero_lt_one.trans hp1).ne' hp
  have hbase : weightedBaseToPair w ψ = periodOnePotential φ.val := by
    rw [← unitBaseEquiv_forgetPairWeight,hψ,unitBaseEquiv_eq,weightedBaseToPair_sourceWeightedPeriodOne]
  have hgs := (sourceWeightedGap_mem hp hp1 w φ.val ψ hbase).summable hp0
  let Q := fun n : ℤ => if M ≤ n.natAbs then
    ‖(w (2*n):ℂ)*sourcePeriodicGapDisplacement hp hp1 φ.val n‖^p.toReal else 0
  have hQ (n : ℤ) : 0 ≤ Q n := by dsimp [Q]; split_ifs <;> positivity
  have hQs : Summable Q := hgs.of_nonneg_of_le hQ (by
    intro n
    dsimp [Q]
    split_ifs
    · rfl
    · positivity)
  let t := weightedResonantCenterClosingTail hp w ψ M
  have hcoord := weightedResonantCenterClosingTail_apply_of_mem hp w ψ M hmem
  have hpoint (n : ℤ) : ‖t.fst n‖^p.toReal+‖t.snd n‖^p.toReal ≤ (2*(2:ℝ)^p.toReal)*Q n := by
    change ‖(weightedResonantCenterClosingTail hp w ψ M).fst n‖^p.toReal+
      ‖(weightedResonantCenterClosingTail hp w ψ M).snd n‖^p.toReal ≤ _
    rw [(hcoord n).1,(hcoord n).2]
    by_cases hn : M ≤ n.natAbs
    · simp only [if_pos hn,Q]
      have hb := hgap n hn
      have hpow (b : ℂ) (hb : ‖b‖ ≤ 2*‖sourcePeriodicGapDisplacement hp hp1 φ.val n‖) :
          ‖(w (2*n):ℂ)*b‖^p.toReal ≤
            (2:ℝ)^p.toReal*‖(w (2*n):ℂ)*sourcePeriodicGapDisplacement hp hp1 φ.val n‖^p.toReal := by
        have hmul : ‖(w (2*n):ℂ)*b‖ ≤ 2*‖(w (2*n):ℂ)*sourcePeriodicGapDisplacement hp hp1 φ.val n‖ := by
          simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (w.positive _),
            mul_left_comm (w (2*n)) 2] using mul_le_mul_of_nonneg_left hb (w.positive (2*n)).le
        have h := Real.rpow_le_rpow (norm_nonneg _) hmul (ENNReal.toReal_nonneg (a := p))
        rwa [Real.mul_rpow (by norm_num) (norm_nonneg _)] at h
      have hm := hpow _ hb.2
      have hp' := hpow _ hb.1
      nlinarith only [hm,hp']
    · simp only [if_neg hn,Q,norm_zero,Real.zero_rpow hp0.ne',mul_zero,add_zero,le_refl]
  rw [CoeffPair.norm_rpow_eq_tsum hp]
  calc
    _ ≤ ∑' n, (2*(2:ℝ)^p.toReal)*Q n :=
      (t.fst.property.summable hp0 |>.add (t.snd.property.summable hp0)).tsum_le_tsum hpoint
        (hQs.mul_left _)
    _ = _ := tsum_mul_left

private theorem sum_rpow_bound (a b r : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 ≤ r) :
    (a+b)^r ≤ (2:ℝ)^r*(a^r+b^r) := by
  have hmax : a+b ≤ 2*max a b := by linarith [le_max_left a b,le_max_right a b]
  calc
    _ ≤ (2*max a b)^r := Real.rpow_le_rpow (add_nonneg ha hb) hmax hr
    _ = (2:ℝ)^r*(max a b)^r := Real.mul_rpow (by norm_num) (ha.trans (le_max_left _ _))
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rcases le_total a b with h | h
      · rw [max_eq_right h]
        exact le_add_of_nonneg_left (Real.rpow_nonneg ha _)
      · rw [max_eq_left h]
        exact le_add_of_nonneg_right (Real.rpow_nonneg hb _)

/-- One quantitative forced Fourier-tail recurrence works for every member
of a compact compatible weighted real-source family and every larger cutoff. -/
theorem source_weighted_fourierTail_forced_recurrence_on_compact
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    {T : Type*} [TopologicalSpace T] [CompactSpace T]
    (φ : T → realTypeSourceSubmodule p) (ψ : T → WeightedCoeffPair w.toWeight p)
    (hφ : Continuous φ) (hψ : Continuous ψ)
    (hrel : ∀ t, w.forgetPairWeight (ψ t) = sourceWeightedPeriodOne (φ t).val) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ t, ∀ N : ℕ, N₀ ≤ N →
      ‖weightedPairFourierTail w.toWeight (2*(4*N)) (ψ t)‖^p.toReal ≤
        (2:ℝ)^p.toReal *
          ((2*(2:ℝ)^p.toReal)*sourceWeightedGapPowerTail hp hp1 w (φ t).val (4*N) +
            offDiagonalSummationConstant p * ‖ψ t‖^p.toReal *
              (‖ψ t‖^(2*p.toReal)/(4*N:ℝ)^(min 1 (p.toReal-1)) +
                ‖weightedPairFourierTail w.toWeight (2*N) (ψ t)‖^(2*p.toReal))) := by
  obtain ⟨N₁,hN₁,hgap⟩ := exists_compact_weightedResonantCenter_gap_bound hp hp1 w φ ψ hφ hψ hrel
  obtain ⟨N₂,_,hrem⟩ := exists_compact_weightedResonantCenterRemainder_bound hp hp1 w ψ hψ
  refine ⟨max N₁ N₂,by omega,fun t N hN => ?_⟩
  have heven (k : ℤ) : (ψ t).fst.val (2*k+1) = 0 ∧ (ψ t).snd.val (2*k+1) = 0 := by
    constructor
    · have h := congrArg (fun a : WeightedCoeffPair SpectralWeight.one.toWeight p => a.fst.val (2*k+1)) (hrel t)
      simpa using h
    · have h := congrArg (fun a : WeightedCoeffPair SpectralWeight.one.toWeight p => a.snd.val (2*k+1)) (hrel t)
      simpa using h
  have hc := weightedResonantCenterClosingTail_le_of_gap_bound hp hp1 (φ t) w (ψ t)
    (hrel t) (4*N) (hrem t (4*N) (by omega)).1
      (fun n hn => hgap t n (by omega))
  have hlead : ‖weightedResonantLeadingTailCLM hp w (4*N) (ψ t)‖ ≤
      ‖weightedResonantCenterClosingTail hp w (ψ t) (4*N)‖+
        ‖weightedResonantCenterRemainder hp w (ψ t) (4*N)‖ := by
    have he : weightedResonantLeadingTailCLM hp w (4*N) (ψ t) =
        weightedResonantCenterClosingTail hp w (ψ t) (4*N)-
          weightedResonantCenterRemainder hp w (ψ t) (4*N) := by
      simp only [weightedResonantCenterClosingTail,add_sub_cancel_right]
    rw [he]
    exact norm_sub_le _ _
  have hpw := (Real.rpow_le_rpow (norm_nonneg _) hlead (ENNReal.toReal_nonneg (a := p))).trans
    (sum_rpow_bound _ _ _ (norm_nonneg _) (norm_nonneg _) ENNReal.toReal_nonneg)
  have hbound := hpw.trans (mul_le_mul_of_nonneg_left
    (add_le_add hc (hrem t (4*N) (by omega)).2) (by positivity))
  change ‖weightedResonantLeadingTail w (ψ t) (4*N)‖^p.toReal ≤ _ at hbound
  rw [norm_weightedResonantLeadingTail_eq_of_even hp w (ψ t) heven,
    show 4*N/2 = 2*N by omega] at hbound
  simpa only [Nat.cast_mul,Nat.cast_ofNat] using hbound

end NLS.ZakharovShabat
