import NLS.ZakharovShabat.ConstantResonantCoefficient
import NLS.ZakharovShabat.WeightedContraction

/-!
# The missing reality hypothesis in the printed Lemma 6.7(ii)

For constant components `(1,i)`, the diagonal correction at a positive real
resonance is `i/(2πn)`. This is not real, even at arbitrarily large frequencies
where the source's half-size contraction holds. Thus the printed unconditional
reality clause cannot hold for general complex potentials. The proof in the
source assumes `φ* = ±φ`; that hypothesis is needed for the reality conclusion.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At a nonzero central lattice parameter, constant components have diagonal correction `ab/(2πn)`. -/
theorem weightedResonantA_constant_center (hp : p ≠ ⊤) (w : SpectralWeight) (a b : ℂ)
    (n : ℤ) (hn : n ≠ 0)
    (h : ‖weightedPotentialSquareInShift hp w (constantSpectralPotential w a b) n
      ((Real.pi : ℂ) * n) (center_mem_resonantStrip n)‖ < 1) :
    weightedResonantA hp w (constantSpectralPotential w a b) n ((Real.pi : ℂ) * n)
      (center_mem_resonantStrip n) h = a * b / ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) := by
  rw [weightedResonantA_constant, complementarySymbol, if_neg (by omega : -n ≠ n)]
  have hd : (Real.pi : ℂ) * n - (Real.pi : ℂ) * (-n : ℤ) = ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hd]
  rfl

/-- The constant complex potential `(1,i)` has strictly positive imaginary diagonal at every positive resonance. -/
theorem constantResonantA_im_pos (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ) (hn : 0 < n)
    (h : ‖weightedPotentialSquareInShift hp w (constantSpectralPotential w 1 Complex.I) n
      ((Real.pi : ℂ) * n) (center_mem_resonantStrip n)‖ < 1) :
    0 < (weightedResonantA hp w (constantSpectralPotential w 1 Complex.I) n ((Real.pi : ℂ) * n)
      (center_mem_resonantStrip n) h).im := by
  rw [weightedResonantA_constant_center hp w 1 Complex.I n hn.ne' h]
  simp only [one_mul, Complex.div_ofReal_im, Complex.I_im]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

/-- Conjugation does not fix this coefficient although the spectral parameter is real. -/
theorem constantResonantA_not_real (hp : p ≠ ⊤) (w : SpectralWeight) (n : ℤ) (hn : 0 < n)
    (h : ‖weightedPotentialSquareInShift hp w (constantSpectralPotential w 1 Complex.I) n
      ((Real.pi : ℂ) * n) (center_mem_resonantStrip n)‖ < 1) :
    (starRingEnd ℂ) (weightedResonantA hp w (constantSpectralPotential w 1 Complex.I) n ((Real.pi : ℂ) * n)
      (center_mem_resonantStrip n) h) ≠
      weightedResonantA hp w (constantSpectralPotential w 1 Complex.I) n ((Real.pi : ℂ) * n)
        (center_mem_resonantStrip n) h := by
  intro he
  have hi := congrArg Complex.im he
  rw [Complex.conj_im] at hi
  linarith [constantResonantA_im_pos hp w n hn h]

/-- No large-frequency cutoff repairs the unconditional reality assertion: the counterexample
satisfies the source's half-size contraction at arbitrarily large positive indices. -/
theorem exists_large_nonreal_resonantA (hp : p ≠ ⊤) (w : SpectralWeight) (M : ℕ) :
    ∃ n : ℤ, (M : ℤ) ≤ n ∧ 0 < n ∧
      ∃ h : ‖weightedPotentialSquareInShift hp w (constantSpectralPotential w 1 Complex.I) n
        ((Real.pi : ℂ) * n) (center_mem_resonantStrip n)‖ < 1,
        ‖weightedPotentialSquareInShift hp w (constantSpectralPotential w 1 Complex.I) n
          ((Real.pi : ℂ) * n) (center_mem_resonantStrip n)‖ ≤ 1/2 ∧
        (starRingEnd ℂ) (weightedResonantA hp w (constantSpectralPotential w 1 Complex.I) n ((Real.pi : ℂ) * n)
          (center_mem_resonantStrip n) h) ≠
          weightedResonantA hp w (constantSpectralPotential w 1 Complex.I) n ((Real.pi : ℂ) * n)
            (center_mem_resonantStrip n) h := by
  let φ := constantSpectralPotential (p := p) w 1 Complex.I
  obtain ⟨N, hN, U, _, _, hφ, _, _, hb⟩ := exists_uniform_complementarySquare_half hp w φ
  let n : ℤ := (max N M : ℕ)
  have hnN : N ≤ n.natAbs := by simpa only [n, Int.natAbs_natCast] using le_max_left N M
  have hnM : (M : ℤ) ≤ n := by
    dsimp [n]
    exact_mod_cast le_max_right N M
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast zero_lt_one.trans_le (hN.trans (le_max_left N M))
  have hhalf := (hb φ hφ n hnN ((Real.pi : ℂ) * n) (center_mem_resonantStrip n)).1
  have h : ‖weightedPotentialSquareInShift hp w φ n ((Real.pi : ℂ) * n) (center_mem_resonantStrip n)‖ < 1 :=
    hhalf.trans_lt (by norm_num)
  exact ⟨n, hnM, hn, h, hhalf, constantResonantA_not_real hp w n hn h⟩

end NLS.ZakharovShabat
