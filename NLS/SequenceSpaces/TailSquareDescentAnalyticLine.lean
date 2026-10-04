import NLS.ComplexAnalysis.AnalyticLineLimit
import NLS.SequenceSpaces.TailSquareDescentFiniteLine

/-! # Analytic slices in arbitrary sequence directions

At finite source exponents, truncations approximate every direction in
the mixed-coordinate norm. Continuity and the analytic line-limit theorem
upgrade finite-support analyticity to full-norm analytic slices along
every complex line. Joint Fréchet analyticity is not asserted here.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Finite-support line analyticity and norm continuity imply analyticity
along every sequence direction at a finite source exponent. -/
theorem analyticOnNhd_line_of_finiteLines (hq : q ≠ ⊤)
    (f : (Coeff q × Coeff q) → F) (U : Set (Coeff q × Coeff q))
    (hU : IsOpen U) (hf : ContinuousOn f U)
    (han : ∀ a ∈ U, ∀ (T : Finset ℤ) (d : Coeff q × Coeff q),
      AnalyticOnNhd ℂ (fun t : ℂ => f (a+t • truncatePair T d))
        ((fun t : ℂ => a+t • truncatePair T d) ⁻¹' U))
    (a d : Coeff q × Coeff q) :
    AnalyticOnNhd ℂ (fun t : ℂ => f (a+t • d)) ((fun t : ℂ => a+t • d) ⁻¹' U) := by
  apply ComplexAnalysis.analyticOnNhd_line_of_tendsto_directions f U hU hf d
    (fun T : Finset ℤ => truncatePair T d) atTop (tendsto_truncatePair hq d) _ a
  intro b hb
  exact Eventually.of_forall (fun T => han b hb T d)

variable {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)] [p.HolderTriple p q]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] in
/-- The half exponent of a finite doubling Holder triple is finite. -/
theorem doublingExponent_ne_top (hp : p ≠ ⊤) : q ≠ ⊤ := by
  let : p.HolderTriple p (p/2) := holderTriple_half p
  have he : q = p/2 := ENNReal.HolderTriple.unique p p q (p/2)
  rw [he]
  exact ENNReal.div_ne_top hp (by norm_num)

/-- The descended sequence map is analytic in the full target norm along
every complex affine line on the line's open intersection with its domain. -/
theorem analyticOnNhd_tailSquareDescent_line (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → Coeff r) (V : Set (Coeff p × Coeff p))
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hinv : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z)
    (b d : Coeff q × Coeff q) :
    AnalyticOnNhd ℂ (fun t : ℂ => tailSquareDescent S f V (b+t • d))
      ((fun t : ℂ => b+t • d) ⁻¹' (pairMixedSquare S '' V)) := by
  apply analyticOnNhd_line_of_finiteLines (doublingExponent_ne_top (q := q) hp)
    (tailSquareDescent S f V) _ (isOpenMap_pairMixedSquare hp S V hV)
    (continuousOn_tailSquareDescent (q := q) hp S f V hV hf.continuousOn hinv) _ b d
  intro a _ T v
  exact analyticOnNhd_tailSquareDescent_finiteLine hp S f V hV hf hinv a T v

end NLS.Coeff
