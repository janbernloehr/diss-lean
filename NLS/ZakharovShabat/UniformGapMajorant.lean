import NLS.ZakharovShabat.ResonantGapMajorant

/-!
# Corrected locally uniform weighted gap power tails

Only leading and off-diagonal remainder terms enter this budget. In particular,
there is no diagonal contribution and no extra potential-norm factor on the
leading Fourier tail. One open convex neighborhood controls all larger cutoffs.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A corrected weighted gap budget with the sharper off-diagonal remainder term. -/
def rootGapBudget (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) : ℝ :=
  rootGapSummationConstant p *
    (‖weightedPairFourierTail w.toWeight (N/2) φ‖^p.toReal +
      offDiagonalSummationConstant p * ‖φ‖^p.toReal *
        (‖φ‖^(2*p.toReal)/(N : ℝ)^(min 1 (p.toReal-1)) +
          ‖weightedPairFourierTail w.toWeight (N/2) φ‖^(2*p.toReal)))

/-- The gap majorant series is exactly the sum of its three convergent components. -/
theorem resonantGapMajorant_tail_sum (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ)
    (hl : Summable (fun n : ℤ => if N ≤ n.natAbs then resonantLeadingPower w φ n else 0))
    (hm : Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w φ n)^p.toReal else 0))
    (hb : Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w φ n)^p.toReal else 0)) :
    Summable (fun n : ℤ => if N ≤ n.natAbs then resonantGapMajorant hp w φ n else 0) ∧
      (∑' n : ℤ, if N ≤ n.natAbs then resonantGapMajorant hp w φ n else 0) =
        rootGapSummationConstant p *
          ((∑' n : ℤ, if N ≤ n.natAbs then resonantLeadingPower w φ n else 0) +
            (∑' n : ℤ, if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w φ n)^p.toReal else 0) +
            (∑' n : ℤ, if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w φ n)^p.toReal else 0)) := by
  have hs := ((hl.hasSum.add hm.hasSum).add hb.hasSum).mul_left (rootGapSummationConstant p)
  have he := hs.congr_fun (g := fun n : ℤ => if N ≤ n.natAbs then resonantGapMajorant hp w φ n else 0)
    (fun n => by by_cases hn : N ≤ n.natAbs <;> simp [resonantGapMajorant, hn])
  exact ⟨he.summable,he.tsum_eq⟩

/-- Locally uniform weighted gap majorants are summable and control every pair of strip roots. -/
theorem exists_uniform_resonantGapMajorant (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        Summable (fun n : ℤ => if N ≤ n.natAbs then resonantGapMajorant hp w ψ n else 0) ∧
        (∑' n : ℤ, if N ≤ n.natAbs then resonantGapMajorant hp w ψ n else 0) ≤ rootGapBudget w ψ N ∧
        ∀ n : ℤ, N ≤ n.natAbs → ∀ x ∈ resonantStrip n, ∀ y ∈ resonantStrip n,
          resonantDeterminantExtension hp w ψ n x = 0 → resonantDeterminantExtension hp w ψ n y = 0 →
            (w (2*n)*‖x-y‖)^p.toReal ≤ resonantGapMajorant hp w ψ n := by
  obtain ⟨N₁,_,U₁,ho₁,hc₁,hφ₁,h0₁,hgap⟩ := exists_uniform_resonantRoot_gap hp hp1 w φ
  obtain ⟨N₂,hN₂,U₂,ho₂,hc₂,hφ₂,h0₂,hoff⟩ := exists_uniform_offDiagonalSup hp hp1 w φ
  refine ⟨max N₁ N₂,hN₂.trans (le_max_right _ _),U₁ ∩ U₂,ho₁.inter ho₂,hc₁.inter hc₂,
    ⟨hφ₁,hφ₂⟩,⟨h0₁,h0₂⟩,?_⟩
  intro ψ hψ N hN
  have hN2 : 2 ≤ N := hN₂.trans (by omega)
  have hb (n : ℤ) (hn : N ≤ n.natAbs) := hoff ψ hψ.2 N (by omega) n hn
  obtain ⟨hsL,hL⟩ := resonantLeadingPower_tail_summable_and_le hp w ψ N (N/2) (by omega)
  obtain ⟨hsM,hM⟩ := resonantBMinusSup_tail_summable_and_le hp hp1 w ψ N hN2 (fun n hn => (hb n hn).1)
  obtain ⟨hsP,hP⟩ := resonantBPlusSup_tail_summable_and_le hp hp1 w ψ N hN2 (fun n hn => (hb n hn).2.1)
  have hE : (∑' n : ℤ, if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w ψ n)^p.toReal else 0) +
      (∑' n : ℤ, if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w ψ n)^p.toReal else 0) ≤
      offDiagonalSummationConstant p * ‖ψ‖^p.toReal *
        (‖ψ‖^(2*p.toReal)/(N : ℝ)^(min 1 (p.toReal-1)) + ‖weightedPairFourierTail w.toWeight (N/2) ψ‖^(2*p.toReal)) := by
    apply (add_le_add hM hP).trans_eq
    rw [norm_withLp_prod_rpow hp ψ]
    ring
  have hsum := resonantGapMajorant_tail_sum hp w ψ N hsL hsM hsP
  refine ⟨hsum.1,?_,?_⟩
  · rw [hsum.2]
    unfold rootGapBudget
    apply mul_le_mul_of_nonneg_left _ (rootGapSummationConstant_nonneg p)
    linarith
  · intro n hn x hx y hy hx0 hy0
    exact resonantRoots_gap_le_majorant hp w ψ n (hb n hn).1.1 (hb n hn).2.1.1 (hb n hn).2.2 x y
      ((hgap ψ hψ.1 n (by omega)).2.2 x hx y hy hx0 hy0)

end NLS.ZakharovShabat
