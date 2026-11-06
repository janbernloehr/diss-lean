import NLS.SequenceSpaces.BoundedCoordinateAnalytic
import NLS.SequenceSpaces.FunctionOrZero

/-! # Weighted analyticity from actual complex coordinate norm comparison

Weak analytic coordinates and a common COMPLEX weighted sequence majorant
prove stronger sequence analyticity. Genuine membership rules out the total
constructor fallback. A real-source membership statement alone is not used.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.Coeff

/-- The literal weighted coefficient function, with a total zero fallback. -/
def weightedSequenceRealization {E : Type*} (w : ℤ → ℂ) (Z : E → Coeff 2) (x : E) : Coeff 2 :=
  ofFunctionOrZero 2 (fun n => w n*Z x n)

/-- A native locally bounded COMPLEX norm majorant and actual scalar
analyticity give the analytic literal weighted sequence, with exact values. -/
theorem analytic_weightedSequenceRealization_of_complex_norm_comparison
    {E P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    (L : E →L[ℂ] P) (U : Set P) (Z : P → Coeff 2) (hZa : AnalyticOnNhd ℂ Z U)
    (w : ℤ → ℂ) (V : Set E) (hV : IsOpen V) (hVU : ∀ p∈V, L p∈U)
    (F : E → Coeff 2) (M : ℝ) (hFb : ∀ p∈V, ‖F p‖≤M)
    (he : ∀ p∈V, ∀ n : ℤ, ‖w n*Z (L p) n‖=‖F p n‖) :
    AnalyticOnNhd ℂ (weightedSequenceRealization w (fun p => Z (L p))) V ∧
      ∀ p∈V, ‖weightedSequenceRealization w (fun p => Z (L p)) p‖≤M ∧
        ∀ n : ℤ, weightedSequenceRealization w (fun p => Z (L p)) p n=w n*Z (L p) n := by
  have hmem (p : E) (hp : p∈V) : Memℓp (fun n => w n*Z (L p) n) 2 :=
    (lp.memℓp (F p)).mono' (fun n => (he p hp n).le)
  have hval (p : E) (hp : p∈V) (n : ℤ) :
      weightedSequenceRealization w (fun p => Z (L p)) p n=w n*Z (L p) n :=
    ofFunctionOrZero_apply_of_mem 2 _ (hmem p hp) n
  have hb (p : E) (hp : p∈V) : ‖weightedSequenceRealization w (fun p => Z (L p)) p‖≤M := by
    apply (lp.norm_mono (by norm_num : (2 : ℝ≥0∞)≠0) ?_).trans (hFb p hp)
    intro n
    rw [hval p hp n]
    exact (he p hp n).le
  refine ⟨?_,fun p hp => ⟨hb p hp,hval p hp⟩⟩
  apply analyticOnNhd_of_bounded_coordinatewise _ hV _ M hb
  intro n p hp
  have hc : AnalyticAt ℂ (fun q => Z (L q) n) p :=
    (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).analyticAt _).comp (hZa (L p) (hVU p hp))).comp
      (L.analyticAt p)
  apply (analyticAt_const.mul hc).congr
  filter_upwards [hV.mem_nhds hp] with q hq
  exact (hval q hq n).symm

end NLS.Coeff
