import NLS.ComplexAnalysis.QuadraticEnergySheet
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! Locally uniform convergence descends through a translated square,
including its ramification energy. A bounded set of square-root lifts
suffices; no global continuity of the principal root is assumed. -/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem tendstoLocallyUniformlyOn_of_quadratic_pullback
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) (c : ℂ)
    (h : TendstoLocallyUniformlyOn (fun N z => F N (z^2-c)) (fun z => f (z^2-c)) atTop univ) :
    TendstoLocallyUniformlyOn F f atTop univ := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro E _
  let R : ℝ := ‖E+c‖+2
  have hU := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact (isCompact_closedBall (0:ℂ) R)).mp
    (h.mono (subset_univ _))
  have hmem (y : ℂ) (hy : y ∈ closedBall E 1) : sqrt (y+c) ∈ closedBall (0:ℂ) R := by
    have hsq : ‖sqrt (y+c)‖^2 = ‖y+c‖ := by rw [← norm_pow,complex_sqrt_sq]
    have hdist : ‖y-E‖ ≤ 1 := by simpa only [mem_closedBall,dist_eq_norm] using hy
    have hnorm : ‖y+c‖ ≤ ‖E+c‖+1 := by
      calc
        ‖y+c‖ = ‖(E+c)+(y-E)‖ := by congr 1; ring
        _ ≤ ‖E+c‖+‖y-E‖ := norm_add_le _ _
        _ ≤ ‖E+c‖+1 := by linarith
    change dist (sqrt (y+c)) 0 ≤ R
    rw [dist_zero_right]
    dsimp only [R]
    nlinarith [norm_nonneg (sqrt (y+c)),norm_nonneg (E+c)]
  have henergy : TendstoUniformlyOn F f atTop (closedBall E 1) := by
    rw [Metric.tendstoUniformlyOn_iff] at hU ⊢
    intro ε hε
    filter_upwards [hU ε hε] with N hN y hy
    have ht := hN (sqrt (y+c)) (hmem y hy)
    have he : (sqrt (y+c))^2-c = y := by rw [complex_sqrt_sq]; ring
    simpa only [he] using ht
  refine ⟨closedBall E 1,nhdsWithin_le_nhds ?_,henergy⟩
  exact mem_of_superset (ball_mem_nhds E (by norm_num : (0:ℝ) < 1)) ball_subset_closedBall

end NLS.ComplexAnalysis
