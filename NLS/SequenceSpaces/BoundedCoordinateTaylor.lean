import NLS.SequenceSpaces.BoundedCoordinateHolomorphic
import NLS.ComplexAnalysis.BanachTaylorBoundsOn

/-!
# Uniform Taylor bounds for finite truncations

Analytic scalar coordinates give analytic finite truncations of an
`ℓq`-valued map. A common norm bound for the original map then gives
one bound for every multilinear Taylor coefficient of every finite
truncation, independent of the truncation.
-/

noncomputable section
open Set Metric
open scoped ENNReal ContDiff
namespace NLS.Coeff

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A finite truncation of an `ℓq`-valued map with analytic scalar
coordinates is analytic on the same Banach parameter domain. -/
theorem analyticOnNhd_truncate_of_coordinatewise
    (f : E → Coeff q) {V : Set E}
    (hcoord : ∀ n : ℤ, AnalyticOnNhd ℂ (fun x => f x n) V)
    (s : Finset ℤ) :
    AnalyticOnNhd ℂ (fun x => truncate s (f x)) V := by
  induction s using Finset.induction_on with
  | empty =>
      simpa only [truncate_empty] using
        (analyticOnNhd_const :
          AnalyticOnNhd ℂ (fun _ : E => (0 : Coeff q)) V)
  | @insert n s hn ih =>
      have hsingle : AnalyticOnNhd ℂ
          (fun x : E => (lp.single q n (f x n) : Coeff q)) V := by
        let L : ℂ →L[ℂ] Coeff q :=
          lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) q n
        change AnalyticOnNhd ℂ (fun x : E => L (f x n)) V
        exact L.comp_analyticOnNhd (hcoord n)
      have heq : (fun x : E => truncate (insert n s) (f x)) =
          (fun x : E =>
            (lp.single q n (f x n) : Coeff q) + truncate s (f x)) := by
        funext x
        simp only [truncate,Finset.sum_insert hn]
      rw [heq]
      exact hsingle.add ih

/-- On a ball inside the coordinatewise analytic domain, all finite
truncations have the same geometric bound on their multilinear
Taylor coefficients. -/
theorem exists_uniform_truncate_taylor_bound
    (f : E → Coeff q) {V : Set E} (hVopen : IsOpen V)
    (hcoord : ∀ n : ℤ, AnalyticOnNhd ℂ (fun x => f x n) V)
    (M : ℝ) (hbound : ∀ x ∈ V, ‖f x‖ ≤ M)
    (c : E) (hc : c ∈ V) :
    ∃ R : ℝ, 0 < R ∧ ball c R ⊆ V ∧
      ∀ s : Finset ℤ, ∀ k : ℕ,
        ‖NLS.ComplexAnalysis.complexTaylorSeries
          (fun x : E => truncate s (f x)) c k‖ ≤
          (4*Real.exp 1/R)^k*M := by
  obtain ⟨R,hR,hball⟩ := Metric.isOpen_iff.mp hVopen c hc
  have hM : 0 ≤ M := (norm_nonneg (f c)).trans (hbound c hc)
  refine ⟨R,hR,hball,?_⟩
  intro s k
  let g : E → Coeff q := fun x => truncate s (f x)
  have hganalytic : AnalyticOnNhd ℂ g V :=
    analyticOnNhd_truncate_of_coordinatewise f hcoord s
  have hgsmooth : ContDiffOn ℂ ∞ g (ball c R) :=
    hganalytic.contDiffOn_of_completeSpace.mono hball
  have hgnorm (x : E) (hx : x ∈ ball c R) : ‖g x‖ ≤ M :=
    (norm_truncate_le (ne_of_gt (zero_lt_one.trans_le Fact.out)) s (f x)).trans
      (hbound x (hball hx))
  exact NLS.ComplexAnalysis.norm_complexTaylorSeries_le_on
    g c R M hR hM hgsmooth hgnorm k

end NLS.Coeff
