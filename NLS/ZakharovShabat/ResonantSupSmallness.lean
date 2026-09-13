import NLS.ZakharovShabat.DiagonalSummability
import NLS.ZakharovShabat.OffDiagonalSummability
import NLS.ZakharovShabat.UniformPowerTail

/-!
# Locally uniform smallness of the actual coefficient suprema

The convergent power sums in Lemma 6.8 control each individual supremum.
Their quantitative tail bounds give one open convex neighborhood and a
cutoff for any prescribed positive tolerance.
-/

noncomputable section
open scoped ENNReal Topology
namespace NLS.ZakharovShabat

/-- A small nonnegative power-tail sum bounds each high-frequency value. -/
theorem lt_of_power_tail_sum_lt {P ε : ℝ} (hP : 0 < P) (hε : 0 < ε)
    (S : ℤ → ℝ) (N : ℕ) (hS : ∀ n, N ≤ n.natAbs → 0 ≤ S n)
    (hs : Summable (fun n : ℤ => if N ≤ n.natAbs then (S n)^P else 0))
    (hb : (∑' n : ℤ, if N ≤ n.natAbs then (S n)^P else 0) < ε^P)
    (n : ℤ) (hn : N ≤ n.natAbs) : S n < ε := by
  have hv : (S n)^P ≤ ∑' k : ℤ, if N ≤ k.natAbs then (S k)^P else 0 := by
    have hnonneg (k : ℤ) : 0 ≤ (if N ≤ k.natAbs then (S k)^P else 0) := by
      split_ifs with hk
      · exact Real.rpow_nonneg (hS k hk) _
      · exact le_rfl
    simpa only [Finset.sum_singleton, if_pos hn] using hs.sum_le_tsum {n} (fun k _ => hnonneg k)
  exact (Real.rpow_lt_rpow_iff (hS n hn) hε.le hP).mp (hv.trans_lt hb)

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual diagonal full-strip supremum is arbitrarily small locally uniformly. -/
theorem exists_uniform_resonantDiagonalSup_small (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        0 ≤ resonantDiagonalSup hp w ψ n ∧ resonantDiagonalSup hp w ψ n < ε ∧
        ∀ z ∈ resonantStrip n, ‖weightedResonantAExtension hp w ψ n z‖ < ε := by
  have hP : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  let M := ‖φ‖+1
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨N₁, hN₁, U₁, ho₁, hc₁, hφ₁, h0₁, hb⟩ := exists_uniform_resonantDiagonalSup hp w φ
  obtain ⟨N₂, hN₂, U₂, ho₂, hc₂, hφ₂, h0₂, hnorm, hbudget⟩ :=
    exists_uniform_powerTail_budget hp w φ (by linarith : 0 < p.toReal)
      (by positivity : 0 < min 1 (p.toReal-1))
      (mul_nonneg (diagonalSummationConstant_nonneg (p := p)) (by positivity : 0 ≤ M^p.toReal))
      (Real.rpow_pos_of_pos hε p.toReal)
  let N := max N₁ N₂
  refine ⟨N, hN₂.trans (le_max_right _ _), U₁ ∩ U₂, ho₁.inter ho₂, hc₁.inter hc₂,
    ⟨hφ₁,hφ₂⟩, ⟨h0₁,h0₂⟩, ?_⟩
  intro ψ hψ n hn
  have hbound (k : ℤ) (hk : N ≤ k.natAbs) := hb ψ hψ.1 k ((le_max_left _ _).trans hk)
  have hs := summable_diagonalSup_tail hp hp1 w ψ N (by dsimp [N]; omega)
    (fun k hk => ⟨(hbound k hk).1, (hbound k hk).2.1⟩)
  have hsum := diagonalSup_tail_sum_le_pair hp hp1 w ψ N (by dsimp [N]; omega)
    (fun k hk => ⟨(hbound k hk).1, (hbound k hk).2.1⟩)
  have hψM : ‖w.forgetPairWeight ψ‖ ≤ M := (w.norm_forgetPairWeight_le hp ψ).trans (hnorm ψ hψ.2).le
  have ht : ‖weightedPairFourierTail SpectralWeight.one.toWeight (N/2) (w.forgetPairWeight ψ)‖ ≤
      ‖weightedPairFourierTail w.toWeight (N/2) ψ‖ := by
    rw [← forgetPairWeight_fourierTail]
    exact w.norm_forgetPairWeight_le hp _
  have hsmall : (∑' k : ℤ, if N ≤ k.natAbs then (resonantDiagonalSup hp w ψ k)^p.toReal else 0) < ε^p.toReal := by
    apply hsum.trans_lt
    apply lt_of_le_of_lt _ (hbudget ψ hψ.2 N (le_max_right _ _))
    have hc := diagonalSummationConstant_nonneg (p := p)
    gcongr
  have hsup := lt_of_power_tail_sum_lt (by linarith) hε _ N
    (fun k hk => (hbound k hk).1) hs hsmall n hn
  refine ⟨(hbound n hn).1, hsup, ?_⟩
  intro z hz
  obtain ⟨h, hv⟩ := (hbound n hn).2.2 z hz
  rw [weightedResonantAExtension_eq hp w ψ n z hz h]
  exact hv.trans_lt hsup

/-- Both actual weighted remainder suprema are arbitrarily small on one neighborhood. -/
theorem exists_uniform_offDiagonalSup_small (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ n : ℤ, N ≤ n.natAbs →
        (0 ≤ resonantBMinusRemainderSup hp w ψ n ∧ resonantBMinusRemainderSup hp w ψ n < ε) ∧
        (0 ≤ resonantBPlusRemainderSup hp w ψ n ∧ resonantBPlusRemainderSup hp w ψ n < ε) ∧
        ∀ z ∈ resonantStrip n,
          w (2*n) * ‖weightedResonantBMinusExtension hp w ψ n z - ψ.fst.val (-(2*n))‖ < ε ∧
          w (2*n) * ‖weightedResonantBPlusExtension hp w ψ n z - ψ.snd.val (2*n)‖ < ε := by
  have hP : 1 < p.toReal := (ENNReal.toReal_lt_toReal (by simp) hp).mpr hp1
  let M := ‖φ‖+1
  have hM : 0 < M := by dsimp [M]; positivity
  obtain ⟨N₁, hN₁, U₁, ho₁, hc₁, hφ₁, h0₁, hb⟩ := exists_uniform_offDiagonalSup hp hp1 w φ
  obtain ⟨N₂, hN₂, U₂, ho₂, hc₂, hφ₂, h0₂, hnorm, hbudget⟩ :=
    exists_uniform_powerTail_budget hp w φ (by positivity : 0 < 2*p.toReal)
      (by positivity : 0 < min 1 (p.toReal-1))
      (mul_nonneg (offDiagonalSummationConstant_nonneg p) (by positivity : 0 ≤ M^p.toReal))
      (Real.rpow_pos_of_pos hε p.toReal)
  let N := max N₁ N₂
  refine ⟨N, hN₂.trans (le_max_right _ _), U₁ ∩ U₂, ho₁.inter ho₂, hc₁.inter hc₂,
    ⟨hφ₁,hφ₂⟩, ⟨h0₁,h0₂⟩, ?_⟩
  intro ψ hψ n hn
  have hbound (k : ℤ) (hk : N ≤ k.natAbs) := hb ψ hψ.1 N (le_max_left _ _) k hk
  obtain ⟨hsm, hmm⟩ := resonantBMinusSup_tail_summable_and_le hp hp1 w ψ N (by dsimp [N]; omega)
    (fun k hk => (hbound k hk).1)
  obtain ⟨hsp, hmp⟩ := resonantBPlusSup_tail_summable_and_le hp hp1 w ψ N (by dsimp [N]; omega)
    (fun k hk => (hbound k hk).2.1)
  have hψM : ‖ψ‖ ≤ M := (hnorm ψ hψ.2).le
  have hfst : ‖ψ.fst‖ ≤ M := (WithLp.norm_fst_le _ ψ).trans hψM
  have hsnd : ‖ψ.snd‖ ≤ M := (WithLp.norm_snd_le _ ψ).trans hψM
  have hsmallm : (∑' k : ℤ, if N ≤ k.natAbs then (resonantBMinusRemainderSup hp w ψ k)^p.toReal else 0) < ε^p.toReal := by
    apply hmm.trans_lt
    apply lt_of_le_of_lt _ (hbudget ψ hψ.2 N (le_max_right _ _))
    have hc := offDiagonalSummationConstant_nonneg p
    gcongr
  have hsmallp : (∑' k : ℤ, if N ≤ k.natAbs then (resonantBPlusRemainderSup hp w ψ k)^p.toReal else 0) < ε^p.toReal := by
    apply hmp.trans_lt
    apply lt_of_le_of_lt _ (hbudget ψ hψ.2 N (le_max_right _ _))
    have hc := offDiagonalSummationConstant_nonneg p
    gcongr
  have hm := lt_of_power_tail_sum_lt (by linarith) hε _ N
    (fun k hk => (hbound k hk).1.1) hsm hsmallm n hn
  have hpl := lt_of_power_tail_sum_lt (by linarith) hε _ N
    (fun k hk => (hbound k hk).2.1.1) hsp hsmallp n hn
  exact ⟨⟨(hbound n hn).1.1, hm⟩, ⟨(hbound n hn).2.1.1, hpl⟩,
    fun z hz => ⟨((hbound n hn).2.2 z hz).1.trans_lt hm,
      ((hbound n hn).2.2 z hz).2.trans_lt hpl⟩⟩

end NLS.ZakharovShabat
