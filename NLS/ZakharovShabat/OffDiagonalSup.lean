import NLS.ZakharovShabat.OffDiagonalTailBound

/-!
# Actual weighted full-strip off-diagonal suprema

The supremum is taken over the entire closed, unbounded strip. A uniform
pointwise majorant proves finiteness, nonnegativity, and control of every
actual value. The weight may be pulled outside the supremum.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The weighted supremum of a complex function on the full resonant strip. -/
def weightedStripSup (w : SpectralWeight) (n : ℤ) (f : ℂ → ℂ) : ℝ :=
  sSup ((fun z : ℂ => w (2*n) * ‖f z‖) '' resonantStrip n)

/-- Every pointwise strip bound controls the actual supremum and bounds its image. -/
theorem weightedStripSup_bounds (w : SpectralWeight) (n : ℤ) (f : ℂ → ℂ) (B : ℝ)
    (hb : ∀ z ∈ resonantStrip n, w (2*n) * ‖f z‖ ≤ B) :
    0 ≤ weightedStripSup w n f ∧ weightedStripSup w n f ≤ B ∧
      ∀ z ∈ resonantStrip n, w (2*n) * ‖f z‖ ≤ weightedStripSup w n f := by
  have hbounded : BddAbove ((fun z : ℂ => w (2*n) * ‖f z‖) '' resonantStrip n) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨z,hz,rfl⟩
    exact hb z hz
  have hvalue (z : ℂ) (hz : z ∈ resonantStrip n) : w (2*n) * ‖f z‖ ≤ weightedStripSup w n f :=
    le_csSup hbounded ⟨z,hz,rfl⟩
  refine ⟨(mul_nonneg (w.positive _).le (norm_nonneg _)).trans
    (hvalue _ (center_mem_resonantStrip n)), ?_, hvalue⟩
  unfold weightedStripSup
  have hne : ((fun z : ℂ => w (2*n) * ‖f z‖) '' resonantStrip n).Nonempty :=
    ⟨_, (Real.pi : ℂ)*n, center_mem_resonantStrip n, rfl⟩
  apply csSup_le hne
  rintro _ ⟨z,hz,rfl⟩
  exact hb z hz

/-- On bounded strip images this definition is the weight times the ordinary supremum. -/
theorem weightedStripSup_eq_mul_sup (w : SpectralWeight) (n : ℤ) (f : ℂ → ℂ) (B : ℝ)
    (hb : ∀ z ∈ resonantStrip n, w (2*n) * ‖f z‖ ≤ B) :
    weightedStripSup w n f = w (2*n) * sSup ((fun z : ℂ => ‖f z‖) '' resonantStrip n) := by
  have hw := w.positive (2*n)
  have hbounded : BddAbove ((fun z : ℂ => ‖f z‖) '' resonantStrip n) := by
    refine ⟨B / w (2*n), ?_⟩
    rintro _ ⟨z,hz,rfl⟩
    apply (le_div_iff₀ hw).mpr
    simpa only [mul_comm] using hb z hz
  apply le_antisymm
  · exact (weightedStripSup_bounds w n f _ (fun z hz =>
      mul_le_mul_of_nonneg_left (le_csSup hbounded ⟨z,hz,rfl⟩) hw.le)).2.1
  · have hle : sSup ((fun z : ℂ => ‖f z‖) '' resonantStrip n) ≤ weightedStripSup w n f / w (2*n) := by
      have hne : ((fun z : ℂ => ‖f z‖) '' resonantStrip n).Nonempty :=
        ⟨_, (Real.pi : ℂ)*n, center_mem_resonantStrip n, rfl⟩
      apply csSup_le hne
      rintro _ ⟨z,hz,rfl⟩
      apply (le_div_iff₀ hw).mpr
      simpa only [mul_comm] using (weightedStripSup_bounds w n f B hb).2.2 z hz
    simpa only [mul_comm] using (le_div_iff₀ hw).mp hle

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Weighted full-strip supremum of the actual negative off-diagonal remainder. -/
def resonantBMinusRemainderSup (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) : ℝ :=
  weightedStripSup w n (fun z => weightedResonantBMinusExtension hp w φ n z - φ.fst.val (-(2*n)))

/-- Weighted full-strip supremum of the actual positive off-diagonal remainder. -/
def resonantBPlusRemainderSup (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) : ℝ :=
  weightedStripSup w n (fun z => weightedResonantBPlusExtension hp w φ n z - φ.snd.val (2*n))

/-- Both actual suprema obey the refined bounds uniformly for every larger cutoff. -/
theorem exists_uniform_offDiagonalSup (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∀ ψ ∈ U, ∀ N : ℕ, N₀ ≤ N → ∀ n : ℤ, N ≤ n.natAbs →
        (0 ≤ resonantBMinusRemainderSup hp w ψ n ∧
          resonantBMinusRemainderSup hp w ψ n ≤ offDiagonalTailBound hp w (w.reflection ψ.fst) ψ.snd N n) ∧
        (0 ≤ resonantBPlusRemainderSup hp w ψ n ∧
          resonantBPlusRemainderSup hp w ψ n ≤ offDiagonalTailBound hp w ψ.snd (w.reflection ψ.fst) N n) ∧
        ∀ z ∈ resonantStrip n,
          w (2*n) * ‖weightedResonantBMinusExtension hp w ψ n z - ψ.fst.val (-(2*n))‖ ≤
            resonantBMinusRemainderSup hp w ψ n ∧
          w (2*n) * ‖weightedResonantBPlusExtension hp w ψ n z - ψ.snd.val (2*n)‖ ≤
            resonantBPlusRemainderSup hp w ψ n := by
  obtain ⟨N₀, hN₀, U, ho, hc, hφ, h0, hb⟩ := exists_uniform_offDiagonalTailBound hp hp1 w φ
  refine ⟨N₀, hN₀, U, ho, hc, hφ, h0, ?_⟩
  intro ψ hψ N hN n hn
  have hm := weightedStripSup_bounds w n _ _ (fun z hz => (hb ψ hψ N hN n hn z hz).1)
  have hp' := weightedStripSup_bounds w n _ _ (fun z hz => (hb ψ hψ N hN n hn z hz).2)
  exact ⟨⟨hm.1, hm.2.1⟩, ⟨hp'.1, hp'.2.1⟩, fun z hz => ⟨hm.2.2 z hz, hp'.2.2 z hz⟩⟩

end NLS.ZakharovShabat
