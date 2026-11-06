import NLS.KdV.HillUniformAllContourBounds
import NLS.KdV.HillActiveRegularAnnulus

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- Uniform disc bounds for the actual deflated normalized numerators,
including the own gap. The geometric cutoff precedes both indices. -/
theorem exists_hillSelectedPsi_common_uniform_deflated_disc_charts :
    ∃ δ B : ℝ, ∃ N : ℕ, 0<δ ∧ 0<B ∧ 1≤N ∧ ∀ n : ℕ, ∀ hn : 1≤n,
      ∃ G : ℂ × Coeff 2 → ℂ,
        AnalyticOnNhd ℂ G (univ ×ˢ ball 0 δ) ∧
        (∀ k : ℕ, N≤k →
          AnalyticOnNhd ℂ (hillComplexRegularGapNumerator h0q h0r G k)
            (closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
              (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) ×ˢ ball 0 δ) ∧
          ∀ p∈ball 0 δ, ∀ E∈closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
            (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
            ‖hillComplexRegularGapNumerator h0q h0r G k (E,p)‖≤B) ∧
        ∀ q : RealPeriodOneHillPotential, ‖q.val‖<δ → ∀ E : ℂ,
          G (E,SpectralWeight.one.toCoeff q.val)=hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn E := by
  obtain ⟨δ,S,hδ,hS,hcharts⟩ := exists_hillSelectedPsi_common_uniform_all_contour_charts h0q h0r
  let U : Set (Coeff 2) := ball 0 δ
  obtain ⟨Nb,hNb,hbounds⟩ := exists_hillRegularGapDensity_uniform_active_contour_bounds h0q h0r U δ Subset.rfl
  obtain ⟨Nr,hNr,hroot⟩ := exists_hillFilledFreeGapRoot_bounded_complex_analytic h0q h0r δ
  let N := max Nb Nr
  have hN : 1≤N := hNb.trans (le_max_left _ _)
  refine ⟨δ,2*S,N,hδ,by positivity,hN,?_⟩
  intro n hn
  obtain ⟨G,hGa,hdata,hreal⟩ := hcharts n hn
  let b : ℕ → ℝ := fun k => if hk : 1≤k then
    S/(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) else 0
  have hb (k : ℕ) : 0≤b k := by
    dsimp only [b]
    split_ifs with hk
    · have hR := hillRealGapContour_geometry 0 h0q h0r k hk
      exact div_nonneg hS.le (add_nonneg hR.1 hR.2.1.le)
    · rfl
  have hB : ∀ p∈U, ∀ k : ℕ, 1≤k → True → ∀ E∈sphere (hillRealGapCenter 0 h0q h0r k : ℂ)
      (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
      ‖G (E,p)/hillAbelianComplexRoot 0 h0q h0r (E,p)‖≤b k := by
    intro p hp k hk _ E hE
    simpa only [b,dif_pos hk] using ((hdata p hp k hk).1 E hE).2
  refine ⟨G,hGa,?_,hreal⟩
  intro k hk
  have hkB : Nb≤k := (le_max_left _ _).trans hk
  have hkR : Nr≤k := (le_max_right _ _).trans hk
  have hk1 : 1≤k := hN.trans hk
  have hR : 0<hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k :=
    add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1 (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  refine ⟨?_,?_⟩
  · intro t ht
    exact (analyticAt_const.mul (hGa t ⟨mem_univ _,ht.2⟩)).div
      ((hroot k hkR).1 t ht) (((hroot k hkR).2 t.2 ht.2 t.1 ht.1).2.1)
  · intro p hp E hE
    have hh := ((hbounds G hGa b hb (fun _ => True) hB k hkB trivial p hp).1 E hE)
    apply hh.trans_eq
    dsimp only [b]
    rw [dif_pos hk1]
    field_simp

end NLS.KdV
