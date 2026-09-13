import NLS.ZakharovShabat.DiagonalSummationExponent
import NLS.ZakharovShabat.ResonantDiagonalSup

/-!
# Summability of the actual diagonal strip suprema

Powered Young controls the actual supremum sequence on every tail beyond the
uniform cutoff. Both terms retain unweighted component norms.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- The actual diagonal suprema form an `ℓᵖ` tail, with explicit reciprocal decay. -/
theorem exists_diagonalSupTail (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (hN : 0 < N)
    (hb : ∀ n : ℤ, N ≤ n.natAbs → 0 ≤ resonantDiagonalSup hp w φ n ∧
      resonantDiagonalSup hp w φ n ≤ resonantDiagonalBound hp w φ n) :
    ∃ s : ℝ, s.HolderConjugate (diagonalInnerExponent p).toReal ∧
      s ≤ max p.toReal p.conjExponent.toReal ∧ p.toReal/s = min 1 (p.toReal-1) ∧
      ∃ v : Coeff p,
        (∀ n : ℤ, v n = if N ≤ n.natAbs then (resonantDiagonalSup hp w φ n : ℂ) else 0) ∧
        ‖v‖ ≤ 8*s*‖w.forgetWeight φ.fst‖ *
          (‖w.toCoeff φ.snd‖ * (N : ℝ)^(-(1/s)) + ‖Coeff.fourierTail N (w.toCoeff φ.snd)‖) := by
  have hr := one_lt_diagonalInnerExponent hp hp1
  let : Fact (1 ≤ diagonalInnerExponent p) := ⟨hr.le⟩
  obtain ⟨s, hc, hs, he⟩ := exists_diagonalInnerConjugate hp hp1
  obtain ⟨d, hd, hn⟩ := exists_reciprocalRowTailMajorant_explicit hp hr
    (min_le_left _ _) (min_le_right _ _) hc (w.toCoeff φ.snd) N hN
  let c : ℝ := 2 * ‖w.forgetWeight φ.fst‖
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  let f : ℤ → ℂ := fun n => if N ≤ n.natAbs then (resonantDiagonalSup hp w φ n : ℂ) else 0
  have hdom (n : ℤ) : ‖f n‖ ≤ ‖((c : ℂ) • d) n‖ := by
    simp only [lp.coeFn_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg hc0]
    by_cases h : N ≤ n.natAbs
    · simp only [f, if_pos h, Complex.norm_real, Real.norm_of_nonneg (hb n h).1]
      exact (hb n h).2.trans (mul_le_mul_of_nonneg_left (hd n h) hc0)
    · simp only [f, if_neg h, norm_zero]
      positivity
  let v : Coeff p := ⟨f, (lp.memℓp ((c : ℂ) • d)).mono' hdom⟩
  refine ⟨s, hc, hs, he, v, fun _ => rfl, ?_⟩
  calc
    ‖v‖ ≤ ‖(c : ℂ) • d‖ := lp.norm_mono (ne_of_gt (zero_lt_one.trans hp1)) hdom
    _ = c * ‖d‖ := by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc0]
    _ ≤ c * (4*s * (‖w.toCoeff φ.snd‖ * (N : ℝ)^(-(1/s)) + ‖Coeff.fourierTail N (w.toCoeff φ.snd)‖)) :=
      mul_le_mul_of_nonneg_left hn hc0
    _ = _ := by dsimp [c]; ring

/-- One open convex neighborhood works for summability at every larger cutoff. -/
theorem exists_uniform_diagonalSupTail (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N →
        ∃ s : ℝ, s.HolderConjugate (diagonalInnerExponent p).toReal ∧
          s ≤ max p.toReal p.conjExponent.toReal ∧ p.toReal/s = min 1 (p.toReal-1) ∧
          ∃ v : Coeff p,
            (∀ n : ℤ, v n = if N ≤ n.natAbs then (resonantDiagonalSup hp w ψ n : ℂ) else 0) ∧
            ‖v‖ ≤ 8*s*‖w.forgetWeight ψ.fst‖ *
              (‖w.toCoeff ψ.snd‖ * (N : ℝ)^(-(1/s)) + ‖Coeff.fourierTail N (w.toCoeff ψ.snd)‖) := by
  obtain ⟨N₀, hN₀, U, ho, hc, hφ, h0, hb⟩ := exists_uniform_resonantDiagonalSup hp w φ
  refine ⟨N₀, hN₀, U, ho, hc, hφ, h0, ?_⟩
  intro ψ hψ N hN
  exact exists_diagonalSupTail hp hp1 w ψ N (by omega) (fun n hn =>
    ⟨(hb ψ hψ n (hN.trans hn)).1, (hb ψ hψ n (hN.trans hn)).2.1⟩)

end NLS.ZakharovShabat
