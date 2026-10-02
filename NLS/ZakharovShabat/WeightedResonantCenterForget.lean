import NLS.ZakharovShabat.WeightedResonantDiagonalCenter

/-! # Diagonal centers do not depend on the Fourier weight

The complementary inverse agrees with its unit-weight realization on
the common contraction domain. Uniqueness of the diagonal equation
then identifies the moving centers, and hence both closing equations,
at every sufficiently distant frequency.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At a fixed source, all sufficiently distant diagonal centers and
both off-diagonal values at those centers agree after forgetting the
weight. The assertion includes the actual named centers. -/
theorem exists_weightedResonantCenter_forget
    (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℤ, N ≤ n.natAbs →
      weightedResonantDiagonalCenter hp w φ n =
        weightedResonantDiagonalCenter hp SpectralWeight.one (w.forgetPairWeight φ) n ∧
      weightedResonantBPlusExtension hp w φ n (weightedResonantDiagonalCenter hp w φ n) =
        weightedResonantBPlusExtension hp SpectralWeight.one (w.forgetPairWeight φ) n
          (weightedResonantDiagonalCenter hp SpectralWeight.one (w.forgetPairWeight φ) n) ∧
      weightedResonantBMinusExtension hp w φ n (weightedResonantDiagonalCenter hp w φ n) =
        weightedResonantBMinusExtension hp SpectralWeight.one (w.forgetPairWeight φ) n
          (weightedResonantDiagonalCenter hp SpectralWeight.one (w.forgetPairWeight φ) n) := by
  obtain ⟨Nw,hNw,Uw,_,_,hφw,_,hw⟩ :=
    exists_uniform_weightedResonantDiagonalCenters hp hp1 w φ
  obtain ⟨Nu,_,Uu,_,_,hφu,_,hu⟩ :=
    exists_uniform_weightedResonantDiagonalCenters hp hp1 SpectralWeight.one (w.forgetPairWeight φ)
  obtain ⟨Nc,_,Uc,_,_,hφc,_,_,hc⟩ := exists_uniform_complementarySquare_half hp w φ
  refine ⟨max Nw (max Nu Nc),hNw.trans (le_max_left _ _),?_⟩
  intro n hn
  have hwdata := (hw φ hφw n (by omega)).1
  have hudata := (hu (w.forgetPairWeight φ) hφu n (by omega)).1
  let ζ := weightedResonantDiagonalCenter hp w φ n
  have hz : ζ ∈ resonantStrip n := refinedResonantDisk_subset_strip n hwdata.1
  obtain ⟨hwsmall,husmall⟩ := hc φ hφc n (by omega) ζ hz
  rw [← norm_weightedPotentialSquareInShift_one hp] at husmall
  have hentry (i j : Fin 2) := weightedCorrectionEntryExtension_forget hp w φ n ζ hz
    (hwsmall.trans_lt (by norm_num)) (husmall.trans_lt (by norm_num)) i j
  have ha : weightedResonantAExtension hp w φ n ζ =
      weightedResonantAExtension hp SpectralWeight.one (w.forgetPairWeight φ) n ζ := hentry 0 0
  have hcenter : ζ = weightedResonantDiagonalCenter hp SpectralWeight.one (w.forgetPairWeight φ) n := by
    apply hudata.2.2.2 ζ hz
    rw [← ha]
    exact hwdata.2.2.1
  refine ⟨hcenter,?_,?_⟩
  · change weightedResonantBPlusExtension hp w φ n ζ = _
    calc
      _ = weightedResonantBPlusExtension hp SpectralWeight.one (w.forgetPairWeight φ) n ζ := hentry 1 0
      _ = _ := congrArg (weightedResonantBPlusExtension hp SpectralWeight.one (w.forgetPairWeight φ) n) hcenter
  · change weightedResonantBMinusExtension hp w φ n ζ = _
    calc
      _ = weightedResonantBMinusExtension hp SpectralWeight.one (w.forgetPairWeight φ) n ζ := hentry 0 1
      _ = _ := congrArg (weightedResonantBMinusExtension hp SpectralWeight.one (w.forgetPairWeight φ) n) hcenter

end NLS.ZakharovShabat
