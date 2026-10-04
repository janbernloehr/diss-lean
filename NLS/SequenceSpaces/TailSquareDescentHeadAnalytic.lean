import NLS.SequenceSpaces.TailSquareDescent

/-! # Analyticity in the retained head variables

A finite-head perturbation of the mixed coordinates has an explicit
linear lift. The recovery identity therefore proves analyticity of the
descended function in these variables. Analyticity in the squared tail
variables, especially at their zeros, is not asserted here.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The descended map is analytic along every retained finite-head
perturbation, with values in the full target Banach norm. -/
theorem analyticAt_tailSquareDescent_finiteHead
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → F) (V : Set (Coeff p × Coeff p))
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hinv : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z)
    (z : Coeff p × Coeff p) (hz : z ∈ V) :
    AnalyticAt ℂ (fun b : Coeff q × Coeff q =>
      tailSquareDescent S f V (pairMixedSquare S z+truncatePair S b)) 0 := by
  let L := pairFiniteBlockCLM (p := q) (q := p) S
  let lift : (Coeff q × Coeff q) → (Coeff p × Coeff p) := fun b => z+L b
  have hl : AnalyticAt ℂ lift 0 := analyticAt_const.add (L.analyticAt 0)
  have hl0 : lift 0 = z := by simp [lift]
  have hcomp : AnalyticAt ℂ (f ∘ lift) 0 := by
    apply AnalyticAt.comp (x := 0) _ hl
    simpa only [hl0] using hf z hz
  have ht : Tendsto lift (𝓝 0) (𝓝 z) := by simpa only [hl0] using hl.continuousAt.tendsto
  apply hcomp.congr
  filter_upwards [ht.eventually (hV.mem_nhds hz)] with b hb
  have h := tailSquareDescent_apply (q := q) S f V hinv (lift b) hb
  have he : pairMixedSquare (q := q) S (lift b) = pairMixedSquare S z+truncatePair S b :=
    pairMixedSquare_add_finiteBlock S z b
  rw [he] at h
  exact h.symm

end NLS.Coeff
