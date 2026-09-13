import NLS.ZakharovShabat.DisplacementMajorantSum

/-!
# Locally uniform summable displacement majorants

One potential neighborhood and cutoff control the actual majorant and its
convergent tails for every larger cutoff. The quantitative bound retains
the additive leading Fourier tail and uses an exponent-only constant.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Forgetting a spectral weight converts the diagonal estimate to a weighted pair budget. -/
theorem diagonalSup_tail_sum_le_weightedPair (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (hN : 0 < N)
    (hb : ∀ n : ℤ, N ≤ n.natAbs → 0 ≤ resonantDiagonalSup hp w φ n ∧
      resonantDiagonalSup hp w φ n ≤ resonantDiagonalBound hp w φ n) :
    (∑' n : ℤ, if N ≤ n.natAbs then (resonantDiagonalSup hp w φ n)^p.toReal else 0) ≤
      diagonalSummationConstant p * ‖φ‖^p.toReal *
        (‖φ‖^p.toReal/(N : ℝ)^(min 1 (p.toReal-1)) + ‖weightedPairFourierTail w.toWeight (N/2) φ‖^p.toReal) := by
  apply (diagonalSup_tail_sum_le_pair hp hp1 w φ N hN hb).trans
  have hB := Real.rpow_le_rpow (norm_nonneg _) (w.norm_forgetPairWeight_le hp φ) (ENNReal.toReal_nonneg (a := p))
  have hT := Real.rpow_le_rpow (norm_nonneg _)
    (w.norm_forgetPairWeight_le hp (weightedPairFourierTail w.toWeight (N/2) φ)) (ENNReal.toReal_nonneg (a := p))
  rw [forgetPairWeight_fourierTail] at hT
  have hC := diagonalSummationConstant_nonneg (p := p)
  gcongr

/-- One locally uniform cutoff controls every larger tail of the common actual root majorant. -/
theorem exists_uniform_resonantDisplacementMajorant (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        Summable (fun n : ℤ => if N ≤ n.natAbs then resonantDisplacementMajorant hp w ψ n else 0) ∧
        (∑' n : ℤ, if N ≤ n.natAbs then resonantDisplacementMajorant hp w ψ n else 0) ≤ rootDisplacementBudget w ψ N ∧
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
  have hA := diagonalSup_tail_sum_le_weightedPair hp hp1 w ψ N (by omega) hdiag
  obtain ⟨hsL,hL⟩ := resonantLeadingPower_tail_summable_and_le hp w ψ N (N/2) (by omega)
  obtain ⟨hsM,hM⟩ := resonantBMinusSup_tail_summable_and_le hp hp1 w ψ N hN2 (fun n hn => (hoff n hn).1)
  obtain ⟨hsP,hP⟩ := resonantBPlusSup_tail_summable_and_le hp hp1 w ψ N hN2 (fun n hn => (hoff n hn).2.1)
  have hE : (∑' n : ℤ, if N ≤ n.natAbs then (resonantBMinusRemainderSup hp w ψ n)^p.toReal else 0) +
      (∑' n : ℤ, if N ≤ n.natAbs then (resonantBPlusRemainderSup hp w ψ n)^p.toReal else 0) ≤
      offDiagonalSummationConstant p * ‖ψ‖^p.toReal *
        (‖ψ‖^(2*p.toReal)/(N : ℝ)^(min 1 (p.toReal-1)) + ‖weightedPairFourierTail w.toWeight (N/2) ψ‖^(2*p.toReal)) := by
    apply (add_le_add hM hP).trans_eq
    rw [norm_withLp_prod_rpow hp ψ]
    ring
  refine ⟨(resonantDisplacementMajorant_tail_sum hp w ψ N hsA hsL hsM hsP).1,
    resonantDisplacementMajorant_tail_le_budget hp w ψ N hsA hsL hsM hsP hA hL hE,?_⟩
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

end NLS.ZakharovShabat
