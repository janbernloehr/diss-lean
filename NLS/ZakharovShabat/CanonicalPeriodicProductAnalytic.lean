import NLS.ZakharovShabat.CanonicalPeriodicProductSmooth
import NLS.ComplexAnalysis.BanachSmoothAnalytic

/-!
# Joint Banach-space analyticity of the canonical periodic product

The complex Fréchet Taylor coefficients define a convergent power series in
the full spectral-parameter and potential space. This proves joint analyticity
without choosing continuous eigenvalue labels, including at spectral collisions
and free lattice points.
-/

noncomputable section
open Filter Topology
open scoped ENNReal ContDiff
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The canonical periodic product is jointly analytic in the full Banach product domain. -/
theorem analyticOnNhd_canonicalPeriodicProduct_joint (hp : p ≠ ⊤) (hp1 : 1 < p) :
    AnalyticOnNhd ℂ (fun t : ℂ × PairSpace p => canonicalPeriodicProduct hp t.2 t.1) Set.univ :=
  NLS.ComplexAnalysis.analyticOnNhd_of_complexSmooth _ (contDiff_canonicalPeriodicProduct_joint hp hp1)

/-- The actual Fréchet Taylor series represents the canonical product on its positive-radius ball. -/
theorem hasFPowerSeriesOnBall_canonicalPeriodicProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (t : ℂ × PairSpace p) :
    let q := NLS.ComplexAnalysis.complexTaylorSeries
      (fun t : ℂ × PairSpace p => canonicalPeriodicProduct hp t.2 t.1) t
    0 < q.radius ∧ HasFPowerSeriesOnBall
      (fun t : ℂ × PairSpace p => canonicalPeriodicProduct hp t.2 t.1) q t q.radius := by
  exact ⟨NLS.ComplexAnalysis.complexTaylorSeries_radius_pos _
    (contDiff_canonicalPeriodicProduct_joint hp hp1) t,
    NLS.ComplexAnalysis.hasFPowerSeriesOnBall_of_complexSmooth _
      (contDiff_canonicalPeriodicProduct_joint hp hp1) t⟩

/-- For each fixed spectral parameter, the canonical product is analytic in the original potential. -/
theorem analyticOnNhd_canonicalPeriodicProduct_potential (hp : p ≠ ⊤) (hp1 : 1 < p) (z : ℂ) :
    AnalyticOnNhd ℂ (fun φ : PairSpace p => canonicalPeriodicProduct hp φ z) Set.univ := by
  intro φ _
  exact (analyticOnNhd_canonicalPeriodicProduct_joint hp hp1 (z,φ) (Set.mem_univ _)).comp
    (analyticAt_const.prod analyticAt_id)

/-- Pullback gives joint analyticity for every original weighted potential space. -/
theorem analyticOnNhd_canonicalPeriodicProduct_weighted (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight) :
    AnalyticOnNhd ℂ (fun t : ℂ × WeightedCoeffPair w.toWeight p =>
      canonicalPeriodicProduct hp (weightedBaseToPair w t.2) t.1) Set.univ := by
  intro t _
  have hmap : AnalyticAt ℂ (fun s : ℂ × WeightedCoeffPair w.toWeight p =>
      (s.1,weightedBaseToPair w s.2)) t :=
    analyticAt_fst.prod (((weightedBaseToPair (p := p) w).analyticAt t.2).comp analyticAt_snd)
  have h := (analyticOnNhd_canonicalPeriodicProduct_joint hp hp1
    (t.1,weightedBaseToPair w t.2) (Set.mem_univ _)).comp
      (f := fun s : ℂ × WeightedCoeffPair w.toWeight p => (s.1,weightedBaseToPair w s.2)) hmap
  exact h

/-- Every joint iterated Fréchet derivative is itself Banach-space analytic. -/
theorem analyticOnNhd_iteratedFDeriv_canonicalPeriodicProduct (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℕ) :
    AnalyticOnNhd ℂ (iteratedFDeriv ℂ n
      (fun t : ℂ × PairSpace p => canonicalPeriodicProduct hp t.2 t.1)) Set.univ :=
  (analyticOnNhd_canonicalPeriodicProduct_joint hp hp1).iteratedFDeriv n

end NLS.ZakharovShabat
