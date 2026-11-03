import NLS.KdV.HillHminusOneCanonicalFrequencyGaps
import NLS.KdV.HillHminusOneCriticalPrimitivePeriods
import NLS.KdV.HillHminusOneGapPairUniqueness
import NLS.ComplexAnalysis.SquaredPairGapBound

/-! # A genuine rough l1 majorant for actual Hill energy gaps

The fixed Miura energy translation is retained in the endpoint lifts.
Both lifted endpoints lie in the actual counted canonical frequency pair.
The resulting inequality includes collapsed pairs without ordering roots.
-/
noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
namespace HillHminusMiuraChart

theorem exists_high_endpoint_frequency_lifts (C : HillHminusMiuraChart)
    (r : ℝ) (hrpi : r ≤ Real.pi/4) :
    ∃ M : ℕ, 0 < M ∧ ∀ n : ℕ+, M ≤ (n : ℕ) → ∀ lambda : ℂ,
      lambda ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r/8) →
        sqrt (lambda+C.energyShift) ∈ refinedResonantDisk (n : ℤ) ∧
        (sqrt (lambda+C.energyShift))^2-C.energyShift = lambda := by
  obtain ⟨M,hM,hshift⟩ := exists_high_disc_sqrt_shift_small C.energyShift (Real.pi/4) (Real.pi/16) (by positivity)
  refine ⟨M,hM,?_⟩
  intro n hn lambda hl
  let c : ℝ := Real.pi*(n : ℕ)
  have hc : 0 < c := by dsimp only [c];positivity
  have hroot : sqrt lambda ∈ closedBall ((Real.pi : ℂ)*(n : ℕ)) (r/8) := by
    have hh := sqrt_mem_closedBall_of_energy_disc c (r/8) hc lambda (by
      simpa only [c,ofReal_mul,ofReal_natCast,mul_div_assoc] using ball_subset_closedBall hl)
    simpa only [c,ofReal_mul,ofReal_natCast] using hh
  have hroot' : sqrt lambda ∈ closedBall ((Real.pi : ℂ)*(n : ℕ)) (Real.pi/4) :=
    closedBall_subset_closedBall (by linarith [Real.pi_pos]) hroot
  have hs : ‖sqrt (lambda+C.energyShift)-sqrt lambda‖ < Real.pi/16 := by
    simpa only [sq_sqrt] using (hshift (n : ℕ) hn (sqrt lambda) hroot').2
  constructor
  · change sqrt (lambda+C.energyShift) ∈ ball ((Real.pi : ℂ)*(n : ℤ)) (Real.pi/4)
    rw [Int.cast_natCast]
    apply mem_ball_iff_norm.mpr
    have ht := norm_sub_le_norm_sub_add_norm_sub (sqrt (lambda+C.energyShift))
      (sqrt lambda) ((Real.pi : ℂ)*(n : ℕ))
    have hh := mem_closedBall_iff_norm.mp hroot
    linarith [Real.pi_pos]
  · rw [sq_sqrt,add_sub_cancel_right]

theorem lifted_endpoint_mem_canonical_pair (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain) (n : ℕ+)
    (H : PeriodicEndpointPair (by simp) (C.frequencyPotential q) (n : ℤ)
      (C.canonicalLeft q (n : ℤ)) (C.canonicalRight q (n : ℤ)))
    (lambda : ℂ) (hl : hillHminusRadicand q lambda = 0)
    (hw : sqrt (lambda+C.energyShift) ∈ refinedResonantDisk (n : ℤ)) :
    sqrt (lambda+C.energyShift) = C.canonicalLeft q (n : ℤ) ∨
      sqrt (lambda+C.energyShift) = C.canonicalRight q (n : ℤ) := by
  apply (H.spectrum_iff _ (refinedResonantDisk_subset_strip _ hw)).mp
  apply (canonicalDiscriminant_sq_eq_four_iff_finite (by simp) (by norm_num)
    (C.frequencyPotential q) (C.frequencyPotential_even q) _).mp
  have he := C.trace_shifted_square q hq (sqrt (lambda+C.energyShift))
  rw [sq_sqrt,add_sub_cancel_right] at he
  change hillHminusDiscriminant q lambda = canonicalDiscriminant (by simp) (C.frequencyPotential q) _ at he
  rw [← he]
  exact sub_eq_zero.mp hl

theorem energy_gap_scale_le_canonical_frequency_gap (C : HillHminusMiuraChart)
    (q : PeriodOneHminusOne) (hq : q ∈ C.domain) (n : ℕ+)
    (H : PeriodicEndpointPair (by simp) (C.frequencyPotential q) (n : ℤ)
      (C.canonicalLeft q (n : ℤ)) (C.canonicalRight q (n : ℤ)))
    (l u : ℂ) (hl : hillHminusRadicand q l = 0) (hu : hillHminusRadicand q u = 0)
    (hwl : sqrt (l+C.energyShift) ∈ refinedResonantDisk (n : ℤ))
    (hwu : sqrt (u+C.energyShift) ∈ refinedResonantDisk (n : ℤ)) :
    ‖l-u‖^2/(n : ℕ)^2 ≤ (16*Real.pi^2)*‖C.canonicalFrequencyGapSquares q (n : ℤ)‖ := by
  have hnorm (z : ℂ) (hz : z ∈ refinedResonantDisk (n : ℤ)) : ‖z‖ ≤ 2*Real.pi*(n : ℕ) := by
    have hd : ‖z-(Real.pi : ℂ)*(n : ℕ)‖ ≤ Real.pi/4 := by
      simpa only [refinedResonantDisk,Int.cast_natCast,mem_ball,dist_eq_norm] using
        (mem_ball_iff_norm.mp hz).le
    have ht := norm_le_norm_sub_add z ((Real.pi : ℂ)*(n : ℕ))
    have hcenter : ‖(Real.pi : ℂ)*(n : ℕ)‖ = Real.pi*(n : ℕ) := by
      simp only [norm_mul,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,Complex.norm_natCast]
    rw [hcenter] at ht
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast n.property
    nlinarith [Real.pi_pos]
  have hg := norm_shifted_square_gap_le_of_mem_pair
    (C.canonicalLeft q (n : ℤ)) (C.canonicalRight q (n : ℤ))
    (sqrt (l+C.energyShift)) (sqrt (u+C.energyShift)) C.energyShift (2*Real.pi*(n : ℕ))
    (by positivity) (hnorm _ H.left_mem) (hnorm _ H.right_mem)
    (C.lifted_endpoint_mem_canonical_pair q hq n H l hl hwl)
    (C.lifted_endpoint_mem_canonical_pair q hq n H u hu hwu)
  rw [sq_sqrt,sq_sqrt,add_sub_cancel_right,add_sub_cancel_right] at hg
  rw [C.canonicalFrequencyGapSquares_apply,norm_pow]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℕ)^2)).mpr
  have hs := mul_self_le_mul_self (norm_nonneg (l-u)) hg
  nlinarith only [hs]

/-- A rough-open neighborhood and genuine locally bounded l1 sequence
control every sufficiently high actual tight endpoint pair. -/
theorem exists_frequency_gap_majorant (C : HillHminusMiuraChart)
    (q0 : PeriodOneHminusOne) (hq0 : q0 ∈ C.domain) (r : ℝ) (hrpi : r ≤ Real.pi/4) :
    ∃ M : ℕ, ∃ U : Set PeriodOneHminusOne, ∃ B : ℝ,
      0 < M ∧ U ⊆ C.domain ∧ IsOpen U ∧ q0 ∈ U ∧ 0 ≤ B ∧ ∀ q ∈ U,
        ‖C.canonicalFrequencyGapSquares q‖ ≤ B ∧ ∀ n : ℕ+, M ≤ (n : ℕ) →
          ∀ l u : ℂ, HillHminusHighGapPair q n r l u →
          l ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r/8) →
          u ∈ ball (((Real.pi : ℂ)*(n : ℕ))^2) (Real.pi*(n : ℕ)*r/8) →
            ‖l-u‖^2/(n : ℕ)^2 ≤ (16*Real.pi^2)*‖C.canonicalFrequencyGapSquares q (n : ℤ)‖ := by
  obtain ⟨Mc,U,B,hMc,hUC,hU,hqU,hB,hdata⟩ := C.exists_bounded_canonical_frequency_gaps q0 hq0
  obtain ⟨Ms,hMs,hlift⟩ := C.exists_high_endpoint_frequency_lifts r hrpi
  refine ⟨max Mc Ms,U,B,lt_of_lt_of_le hMc (le_max_left _ _),hUC,hU,hqU,hB,?_⟩
  intro q hq
  refine ⟨(hdata q hq).1,?_⟩
  intro n hn l u hp hl hu
  have hnc : Mc ≤ (n : ℤ).natAbs := by simpa only [Int.natAbs_natCast] using (le_max_left Mc Ms).trans hn
  have hns : Ms ≤ (n : ℕ) := (le_max_right _ _).trans hn
  exact C.energy_gap_scale_le_canonical_frequency_gap q (hUC hq) n ((hdata q hq).2 (n : ℤ) hnc)
    l u hp.left_zero hp.right_zero (hlift n hns l hl).1 (hlift n hns u hu).1

end HillHminusMiuraChart

/-- The tight pair retained in actual cut data controls every unordered
pair on the same disc. One rough neighborhood and cutoff precede them all. -/
theorem HillHminusCriticalPrimitiveCutData.exists_frequency_gap_majorant
    {C : HillHminusMiuraChart} {N M : ℕ} {U : Set PeriodOneHminusOne} {r A : ℝ}
    (H : HillHminusCriticalPrimitiveCutData C N M U r A)
    (hU : IsOpen U) (h0U : 0 ∈ U) (hUC : U ⊆ C.domain) :
    ∃ L : ℕ, ∃ W : Set PeriodOneHminusOne, ∃ B : ℝ,
      0 < L ∧ M ≤ L ∧ W ⊆ U ∧ IsOpen W ∧ 0 ∈ W ∧ 0 ≤ B ∧ ∀ q ∈ W,
        ‖C.canonicalFrequencyGapSquares q‖ ≤ B ∧ ∀ k : ℕ+, L ≤ (k : ℕ) →
          ∀ l u : ℂ, HillHminusHighGapPair q k r l u →
            ‖l-u‖^2/(k : ℕ)^2 ≤ (16*Real.pi^2)*‖C.canonicalFrequencyGapSquares q (k : ℤ)‖ := by
  obtain ⟨Mg,Ug,B,hMg,_,hUg,h0Ug,hB,hg⟩ :=
    C.exists_frequency_gap_majorant 0 (hUC h0U) r H.radius_le
  refine ⟨max M Mg,U ∩ Ug,B,lt_of_lt_of_le hMg (le_max_right _ _),le_max_left _ _,
    inter_subset_left,hU.inter hUg,⟨h0U,h0Ug⟩,hB,?_⟩
  intro q hq
  refine ⟨(hg q hq.2).1,?_⟩
  intro k hk l u hp
  obtain ⟨a,b,F,hpair,ha,hb,_⟩ := H.data q hq.1 k ((le_max_left _ _).trans hk)
  rw [hp.norm_gap_eq hpair]
  exact (hg q hq.2).2 k ((le_max_right _ _).trans hk) a b hpair ha hb

end NLS.KdV
