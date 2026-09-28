import NLS.SequenceSpaces.BoundedCoordinateTaylorAssembly
import NLS.ComplexAnalysis.BanachSmoothAnalyticOn

/-!
# Banach analyticity from bounded analytic coordinates

The assembled Taylor coefficients have a common positive convergence
radius. Their scalar coordinates sum to the scalar coordinate maps,
so the Banach-valued sum equals the original sequence map.
-/

noncomputable section
open Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff
namespace NLS.Coeff

variable {q : ℝ≥0∞} [Fact (1 ≤ q)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A locally bounded `ℓq` map with analytic scalar coordinates is
Banach-space analytic on its open parameter domain. -/
theorem analyticOnNhd_of_bounded_coordinatewise
    (f : E → Coeff q) {V : Set E} (hVopen : IsOpen V)
    (hcoord : ∀ n : ℤ, AnalyticOnNhd ℂ (fun x => f x n) V)
    (M : ℝ) (hbound : ∀ x ∈ V, ‖f x‖ ≤ M) :
    AnalyticOnNhd ℂ f V := by
  classical
  intro c hc
  obtain ⟨R,hR,hball,hcoeff⟩ :=
    exists_taylor_coefficient_of_bounded_coordinatewise
      f hVopen hcoord M hbound c hc
  let p : FormalMultilinearSeries ℂ E (Coeff q) := fun k => Classical.choose (hcoeff k)
  have hpcoord (k : ℕ) (v : Fin k → E) (n : ℤ) :
      p k v n = NLS.ComplexAnalysis.complexTaylorSeries
        (fun x : E => f x n) c k v :=
    (Classical.choose_spec (hcoeff k)).1 v n
  have hpbound (k : ℕ) : ‖p k‖ ≤ (4*Real.exp 1/R)^k*M :=
    (Classical.choose_spec (hcoeff k)).2
  let r₀ : ℝ≥0 := ⟨R/(4*Real.exp 1),by positivity⟩
  let r₁ : ℝ≥0 := ⟨R/3,by positivity⟩
  have hr₀ : 0 < (r₀ : ℝ≥0∞) := by
    exact_mod_cast (show 0 < R/(4*Real.exp 1) by positivity)
  have hr₁ : 0 < (r₁ : ℝ≥0∞) := by
    exact_mod_cast (show 0 < R/3 by positivity)
  have hM : 0 ≤ M := (norm_nonneg (f c)).trans (hbound c hc)
  have hrad : (r₀ : ℝ≥0∞) ≤ p.radius := by
    apply p.le_radius_of_bound M
    intro k
    calc
      _ ≤ ((4*Real.exp 1/R)^k*M)*(r₀ : ℝ)^k :=
        mul_le_mul_of_nonneg_right (hpbound k) (by positivity)
      _ = M := by
        have he : (4*Real.exp 1/R)*(r₀ : ℝ) = 1 := by
          change (4*Real.exp 1/R)*(R/(4*Real.exp 1)) = 1
          field_simp
        calc
          _ = ((4*Real.exp 1/R)*(r₀ : ℝ))^k*M := by rw [mul_pow]; ring
          _ = M := by rw [he, one_pow, one_mul]
  let r : ℝ≥0∞ := min (r₀ : ℝ≥0∞) (r₁ : ℝ≥0∞)
  have hr : 0 < r := lt_min hr₀ hr₁
  have hrle : r ≤ p.radius := (min_le_left _ _).trans hrad
  have hsum (y : E) (hy : y ∈ eball (0 : E) r) :
      HasSum (fun k : ℕ => p k (fun _ : Fin k => y)) (f (c+y)) := by
    have hpsum := p.hasSum (by
      simpa only [mem_eball, edist_zero_right] using
        ((show ‖y‖ₑ < r by
          simpa only [mem_eball, edist_zero_right] using hy).trans_le hrle))
    have hy' : ‖y‖ < R/3 := by
      have hy0 : ‖y‖ₑ < r := by simpa only [mem_eball, edist_zero_right] using hy
      have he' : ‖y‖ₑ < (r₁ : ℝ≥0∞) := hy0.trans_le (min_le_right _ _)
      have he : ENNReal.ofReal ‖y‖ < (r₁ : ℝ≥0∞) := by
        simpa only [ofReal_norm] using he'
      have htR : (r₁ : ℝ≥0∞) = ENNReal.ofReal (R/3) := by
        rw [ENNReal.ofReal_eq_coe_nnreal (by positivity : 0 ≤ R/3)]
        rfl
      rw [htR] at he
      exact (ENNReal.ofReal_lt_ofReal_iff (show 0 < R/3 by positivity)).mp he
    have heq : p.sum y = f (c+y) := by
      ext n
      have hproj := (lp.evalCLM (𝕜 := ℂ) (fun _ : ℤ => ℂ) q n).hasSum hpsum
      have hproj' : HasSum
          (fun k : ℕ => NLS.ComplexAnalysis.complexTaylorSeries
            (fun x : E => f x n) c k (fun _ : Fin k => y))
          (p.sum y n) := by
        change HasSum (fun k : ℕ => p k (fun _ : Fin k => y) n)
          (p.sum y n) at hproj
        simpa only [hpcoord] using hproj
      have hscalar := NLS.ComplexAnalysis.hasSum_complexTaylorSeries_on
        (fun x : E => f x n) hVopen
        ((hcoord n).contDiffOn_of_completeSpace) hc R hR hball hy'
      exact hproj'.unique hscalar
    exact heq ▸ hpsum
  exact ⟨p,r,⟨hrle,hr,fun {y} hy => hsum y hy⟩⟩

end NLS.Coeff
