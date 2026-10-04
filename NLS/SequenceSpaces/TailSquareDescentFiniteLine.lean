import NLS.SequenceSpaces.FiniteMixedSquareLineLift
import NLS.SequenceSpaces.TailSquareDescentAnalyticSlice

/-! # Analyticity along finite-support directions

A squared line parameter admits a simultaneous analytic lift through all
changed tail squares. Scalar square descent and norm-continuous sequence
realization give analytic slices in every finite-support direction. This
does not yet assert analyticity in arbitrary source directions.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- Scalar analytic recovery implies analyticity along any finite-support
mixed-coordinate line, even through multiple zero tail entries. -/
theorem analyticAt_mixedSquare_finiteLine_of_recovery
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → ℂ) (g : (Coeff q × Coeff q) → ℂ)
    (V : Set (Coeff p × Coeff p)) (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hg : ∀ z ∈ V, g (pairMixedSquare S z) = f z)
    (z : Coeff p × Coeff p) (hz : z ∈ V) (T : Finset ℤ) (d : Coeff q × Coeff q) :
    AnalyticAt ℂ (fun t : ℂ => g (pairMixedSquare S z+t • truncatePair T d)) 0 := by
  let lift := pairFiniteMixedSquareLineLift S T z d
  have hl : AnalyticAt ℂ lift 0 := analyticAt_pairFiniteMixedSquareLineLift S T z d
  have hl0 : lift 0 = z := pairFiniteMixedSquareLineLift_zero S T z d
  have hc : AnalyticAt ℂ (f ∘ lift) 0 := by
    apply AnalyticAt.comp (x := 0) _ hl
    simpa only [hl0] using hf z hz
  have ht : Tendsto lift (𝓝 0) (𝓝 z) := by simpa only [hl0] using hl.continuousAt.tendsto
  have hpull : AnalyticAt ℂ (fun u : ℂ => g (pairMixedSquare S z+u^2 • truncatePair T d)) 0 := by
    apply hc.congr
    filter_upwards [ht.eventually (hV.mem_nhds hz)] with u hu
    have he := hg (lift u) hu
    rw [pairMixedSquare_pairFiniteMixedSquareLineLift S T z d u] at he
    exact he.symm
  simpa only [zero_pow (by decide : 2 ≠ 0)] using
    ComplexAnalysis.analyticAt_of_comp_sq (fun t : ℂ => g (pairMixedSquare S z+t • truncatePair T d)) 0 hpull

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Every continuous linear scalar observation of the descent is analytic
along an arbitrary finite-support direction. -/
theorem analyticAt_tailSquareDescent_finiteLine
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → F) (V : Set (Coeff p × Coeff p))
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hinv : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z)
    (z : Coeff p × Coeff p) (hz : z ∈ V) (T : Finset ℤ) (d : Coeff q × Coeff q)
    (L : F →L[ℂ] ℂ) :
    AnalyticAt ℂ (fun t : ℂ => L (tailSquareDescent S f V
      (pairMixedSquare S z+t • truncatePair T d))) 0 := by
  apply analyticAt_mixedSquare_finiteLine_of_recovery S (fun z => L (f z))
    (fun b => L (tailSquareDescent S f V b)) V hV
    (fun z hz => (L.analyticAt _).comp (hf z hz)) _ z hz T d
  intro w hw
  rw [tailSquareDescent_apply S f V hinv w hw]

variable {r : ℝ≥0∞} [Fact (1 ≤ r)]

/-- Finite-support slices are analytic in the full target sequence norm
on their entire open intersection with the mixed-coordinate domain. -/
theorem analyticOnNhd_tailSquareDescent_finiteLine (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → Coeff r) (V : Set (Coeff p × Coeff p))
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hinv : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z)
    (b : Coeff q × Coeff q) (T : Finset ℤ) (d : Coeff q × Coeff q) :
    AnalyticOnNhd ℂ (fun t : ℂ => tailSquareDescent S f V (b+t • truncatePair T d))
      ((fun t : ℂ => b+t • truncatePair T d) ⁻¹' (pairMixedSquare S '' V)) := by
  apply analyticOnNhd_sequenceSlice (tailSquareDescent (q := q) S f V)
    (pairMixedSquare (q := q) S '' V) (isOpenMap_pairMixedSquare hp S V hV)
    (continuousOn_tailSquareDescent (q := q) hp S f V hV hf.continuousOn hinv)
    (ContinuousLinearMap.toSpanSingleton ℂ (truncatePair T d)) _ b
  rintro _ ⟨z,hz,rfl⟩ n
  exact analyticAt_tailSquareDescent_finiteLine S f V hV hf hinv z hz T d
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) r n)

end NLS.Coeff
