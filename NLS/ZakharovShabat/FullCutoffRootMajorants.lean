import NLS.ZakharovShabat.FullCutoffSummability
import NLS.ZakharovShabat.UniformGapMajorant

/-! # Sharper corrected Section 6 cutoff estimates

The original source norms and spectral data are retained. The additive leading-tail
term is not removed; the refuted printed estimates are not asserted.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The corrected estimate retains the leading Fourier tail at the full cutoff. -/
def rootDisplacementBudget_fullCutoff {p : ℝ≥0∞} [Fact (1 ≤ p)] (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) : ℝ :=
  rootDisplacementSummationConstant p *
    (‖weightedPairFourierTail w.toWeight N φ‖^p.toReal +
      (‖φ‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1)) + ‖weightedPairFourierTail w.toWeight N φ‖^p.toReal) *
        (1+‖φ‖^p.toReal)*‖φ‖^p.toReal)

/-- The corrected estimate retains the leading Fourier tail at the full cutoff. -/
def rootGapBudget_fullCutoff (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) : ℝ :=
  rootGapSummationConstant p *
    (‖weightedPairFourierTail w.toWeight N φ‖^p.toReal +
      offDiagonalSummationConstant p * ‖φ‖^p.toReal *
        (‖φ‖^(2*p.toReal)/(N : ℝ)^(min 1 (p.toReal-1)) +
          ‖weightedPairFourierTail w.toWeight N φ‖^(2*p.toReal)))

/-- The corrected estimate retains the leading Fourier tail at the full cutoff. -/
theorem resonantDisplacementMajorant_tail_le_budget_fullCutoff (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ)
    (ha : Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantDiagonalSup hp w φ n)^p.toReal else 0))
    (hl : Summable (fun n : ℤ => if N ≤ n.natAbs then resonantLeadingPower w φ n else 0))
    (hm : Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w φ n)^p.toReal else 0))
    (hb : Summable (fun n : ℤ => if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w φ n)^p.toReal else 0))
    (hA : (∑' n : ℤ, if N ≤ n.natAbs then (resonantDiagonalSup hp w φ n)^p.toReal else 0) ≤
      diagonalSummationConstant p * ‖φ‖^p.toReal *
        (‖φ‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1)) + ‖weightedPairFourierTail w.toWeight N φ‖^p.toReal))
    (hL : (∑' n : ℤ, if N ≤ n.natAbs then resonantLeadingPower w φ n else 0) ≤
      ‖weightedPairFourierTail w.toWeight N φ‖^p.toReal)
    (hE : (∑' n : ℤ, if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w φ n)^p.toReal else 0) +
      (∑' n : ℤ, if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w φ n)^p.toReal else 0) ≤
      offDiagonalSummationConstant p * ‖φ‖^p.toReal *
        (‖φ‖^(2*p.toReal)/(N : ℝ)^(min 1 (p.toReal-1)) + ‖weightedPairFourierTail w.toWeight N φ‖^(2*p.toReal))) :
    (∑' n : ℤ, if N ≤ n.natAbs then resonantDisplacementMajorant hp w φ n else 0) ≤
      rootDisplacementBudget_fullCutoff w φ N := by
  rw [(resonantDisplacementMajorant_tail_sum hp w φ N ha hl hm hb).2]
  have hB2 : ‖φ‖^(2*p.toReal) = (‖φ‖^p.toReal)^2 := by
    rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring
  have hT2 : ‖weightedPairFourierTail w.toWeight N φ‖^(2*p.toReal) =
      (‖weightedPairFourierTail w.toWeight N φ‖^p.toReal)^2 := by
    rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
    congr 1
    ring
  have htail := Real.rpow_le_rpow (norm_nonneg _)
    (norm_weightedPairFourierTail_le hp w.toWeight N φ) (ENNReal.toReal_nonneg (a := p))
  have hc := combine_rootDisplacement_budgets (A := ‖φ‖^p.toReal)
    (T := ‖weightedPairFourierTail w.toWeight N φ‖^p.toReal)
    (D := (N : ℝ)^(min 1 (p.toReal-1))) (K := (2 : ℝ)^(p.toReal-1))
    (by positivity) (by positivity) htail (by positivity) (by positivity)
    (diagonalSummationConstant_nonneg (p := p)) (offDiagonalSummationConstant_nonneg p)
  apply le_trans _ (by simpa only [← hB2, ← hT2, rootDisplacementBudget_fullCutoff, rootDisplacementSummationConstant] using hc)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add hA
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

/-- The corrected estimate retains the leading Fourier tail at the full cutoff. -/
theorem exists_uniform_resonantDisplacementMajorant_fullCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        Summable (fun n : ℤ => if N ≤ n.natAbs then resonantDisplacementMajorant hp w ψ n else 0) ∧
        (∑' n : ℤ, if N ≤ n.natAbs then resonantDisplacementMajorant hp w ψ n else 0) ≤ rootDisplacementBudget_fullCutoff w ψ N ∧
        ∀ n : ℤ, N ≤ n.natAbs → 0 ≤ resonantDisplacementMajorant hp w ψ n ∧
          ∀ x ∈ resonantStrip n, ∀ y ∈ resonantStrip n,
            resonantDeterminantExtension hp w ψ n x = 0 → resonantDeterminantExtension hp w ψ n y = 0 →
              ‖x-(Real.pi : ℂ)*n‖^p.toReal + ‖y-(Real.pi : ℂ)*n‖^p.toReal ≤
                resonantDisplacementMajorant hp w ψ n := by
  obtain ⟨N₁,_,U₁,ho₁,hc₁,hφ₁,h0₁,h₁⟩ := exists_uniform_resonantDiagonalSup hp w φ
  obtain ⟨N₂,hN₂,U₂,ho₂,hc₂,hφ₂,h0₂,h₂⟩ := exists_uniform_offDiagonalSup hp hp1 w φ
  refine ⟨max N₁ N₂,hN₂.trans (le_max_right _ _),U₁ ∩ U₂,ho₁.inter ho₂,hc₁.inter hc₂,
    ⟨hφ₁,hφ₂⟩,⟨h0₁,h0₂⟩,?_⟩
  intro ψ hψ N hN
  have hN2 : 2 ≤ N := hN₂.trans (by omega)
  have hdiag (n : ℤ) (hn : N ≤ n.natAbs) : 0 ≤ resonantDiagonalSup hp w ψ n ∧
      resonantDiagonalSup hp w ψ n ≤ resonantDiagonalBound hp w ψ n :=
    ⟨(h₁ ψ hψ.1 n (by omega)).1,(h₁ ψ hψ.1 n (by omega)).2.1⟩
  have hoff (n : ℤ) (hn : N ≤ n.natAbs) := h₂ ψ hψ.2 N (by omega) n hn
  have hsA := summable_diagonalSup_tail hp hp1 w ψ N (by omega) hdiag
  have hA := diagonalSup_tail_sum_le_weightedPair_fullCutoff hp hp1 w ψ N (by omega) hdiag
  obtain ⟨hsL,hL⟩ := resonantLeadingPower_tail_summable_and_le hp w ψ N N (by omega)
  obtain ⟨hsM,hM⟩ := resonantBMinusSup_tail_summable_and_le_fullCutoff hp hp1 w ψ N hN2 (fun n hn => (hoff n hn).1)
  obtain ⟨hsP,hP⟩ := resonantBPlusSup_tail_summable_and_le_fullCutoff hp hp1 w ψ N hN2 (fun n hn => (hoff n hn).2.1)
  have hE : (∑' n : ℤ, if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w ψ n)^p.toReal else 0) +
      (∑' n : ℤ, if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w ψ n)^p.toReal else 0) ≤
      offDiagonalSummationConstant p * ‖ψ‖^p.toReal *
        (‖ψ‖^(2*p.toReal)/(N : ℝ)^(min 1 (p.toReal-1)) + ‖weightedPairFourierTail w.toWeight N ψ‖^(2*p.toReal)) := by
    apply (add_le_add hM hP).trans_eq
    rw [norm_withLp_prod_rpow hp ψ]
    ring
  refine ⟨(resonantDisplacementMajorant_tail_sum hp w ψ N hsA hsL hsM hsP).1,
    resonantDisplacementMajorant_tail_le_budget_fullCutoff hp w ψ N hsA hsL hsM hsP hA hL hE,?_⟩
  intro n hn
  refine ⟨resonantDisplacementMajorant_nonneg hp w ψ n (hdiag n hn).1 (hoff n hn).1.1 (hoff n hn).2.1.1,?_⟩
  intro x hx y hy hx0 hy0
  apply resonantRoots_displacement_le_majorant hp w ψ n ?_ x y hx hy hx0 hy0
  intro z hz
  obtain ⟨hsmall,ha⟩ := (h₁ ψ hψ.1 n (by omega)).2.2 z hz
  rw [← weightedResonantAExtension_eq hp w ψ n z hz hsmall] at ha
  have hrem := (hoff n hn).2.2 z hz
  exact ⟨ha,(le_mul_of_one_le_left (norm_nonneg _) (w.one_le _)).trans hrem.1,
    (le_mul_of_one_le_left (norm_nonneg _) (w.one_le _)).trans hrem.2⟩

/-- The corrected estimate retains the leading Fourier tail at the full cutoff. -/
theorem exists_uniform_resonantGapMajorant_fullCutoff (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        Summable (fun n : ℤ => if N ≤ n.natAbs then resonantGapMajorant hp w ψ n else 0) ∧
        (∑' n : ℤ, if N ≤ n.natAbs then resonantGapMajorant hp w ψ n else 0) ≤ rootGapBudget_fullCutoff w ψ N ∧
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
  obtain ⟨hsL,hL⟩ := resonantLeadingPower_tail_summable_and_le hp w ψ N N (by omega)
  obtain ⟨hsM,hM⟩ := resonantBMinusSup_tail_summable_and_le_fullCutoff hp hp1 w ψ N hN2 (fun n hn => (hb n hn).1)
  obtain ⟨hsP,hP⟩ := resonantBPlusSup_tail_summable_and_le_fullCutoff hp hp1 w ψ N hN2 (fun n hn => (hb n hn).2.1)
  have hE : (∑' n : ℤ, if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w ψ n)^p.toReal else 0) +
      (∑' n : ℤ, if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w ψ n)^p.toReal else 0) ≤
      offDiagonalSummationConstant p * ‖ψ‖^p.toReal *
        (‖ψ‖^(2*p.toReal)/(N : ℝ)^(min 1 (p.toReal-1)) + ‖weightedPairFourierTail w.toWeight N ψ‖^(2*p.toReal)) := by
    apply (add_le_add hM hP).trans_eq
    rw [norm_withLp_prod_rpow hp ψ]
    ring
  have hsum := resonantGapMajorant_tail_sum hp w ψ N hsL hsM hsP
  refine ⟨hsum.1,?_,?_⟩
  · rw [hsum.2]
    unfold rootGapBudget_fullCutoff
    apply mul_le_mul_of_nonneg_left _ (rootGapSummationConstant_nonneg p)
    linarith
  · intro n hn x hx y hy hx0 hy0
    exact resonantRoots_gap_le_majorant hp w ψ n (hb n hn).1.1 (hb n hn).2.1.1 (hb n hn).2.2 x y
      ((hgap ψ hψ.1 n (by omega)).2.2 x hx y hy hx0 hy0)

end NLS.ZakharovShabat
