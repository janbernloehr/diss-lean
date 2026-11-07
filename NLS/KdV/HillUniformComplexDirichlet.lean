import NLS.KdV.HillScaledComplexZeroCounts
import NLS.ComplexAnalysis.LogarithmicSingleRootMoment

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillScaledDirichletRoot (ρ : ℝ) (k : ℕ) (p : Coeff 2) : ℂ :=
  logarithmicCircleMoment (fun t : ℂ × Coeff 2 => hillL2DirichletCharacteristic t.2 t.1)
    (hillRealGapCenter 0 h0q h0r k : ℂ)
    (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)) 1 p

theorem exists_hillScaledDirichletRoot_bounded_complex_analytic_chart
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ k : ℕ, N ≤ k →
      AnalyticOnNhd ℂ (hillScaledDirichletRoot h0q h0r ρ k) (ball (0 : Coeff 2) B) ∧
      ∀ p : Coeff 2, ‖p‖ ≤ B →
        hillScaledDirichletRoot h0q h0r ρ k p ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ)
          (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)) ∧
        hillL2DirichletCharacteristic p (hillScaledDirichletRoot h0q h0r ρ k p)=0 ∧
        analyticOrderAt (hillL2DirichletCharacteristic p) (hillScaledDirichletRoot h0q h0r ρ k p)=1 ∧
        ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
          (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)),
          hillL2DirichletCharacteristic p E=0 ↔ E=hillScaledDirichletRoot h0q h0r ρ k p := by
  obtain ⟨N,hN,hroots⟩ := exists_hillScaledFreeGapContour_bounded_complex_Dirichlet_roots h0q h0r ρ hρ hρ1 B
  refine ⟨N,hN,?_⟩
  intro k hk
  have hR := mul_pos hρ (add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k (hN.trans hk)).1
    (hillRealGapContour_geometry 0 h0q h0r k (hN.trans hk)).2.1)
  have hpB (p : Coeff 2) (hp : p ∈ ball (0 : Coeff 2) B) : ‖p‖ ≤ B :=
    (show ‖p‖ < B by simpa only [mem_ball,dist_zero_right] using hp).le
  have han := analyticOnNhd_logarithmicCircleMoment_of_isOpen
    (fun t : ℂ × Coeff 2 => hillL2DirichletCharacteristic t.2 t.1) analyticOnNhd_hillL2DirichletCharacteristic_joint
    (hillRealGapCenter 0 h0q h0r k : ℂ)
    (ρ*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)) hR.le 1 isOpen_ball
    (fun p hp => (hroots p (hpB p hp) k hk).1)
  refine ⟨han,?_⟩
  intro p hp
  obtain ⟨hb,a,ha,haz,horder,hm,hunique⟩ := hroots p hp k hk
  have he : hillScaledDirichletRoot h0q h0r ρ k p=a := by
    exact (logarithmicCircleMoment_eq_single_root_power
      (fun t : ℂ × Coeff 2 => hillL2DirichletCharacteristic t.2 t.1) p hR 1
      ((analyticOnNhd_hillL2DirichletCharacteristic p).mono (subset_univ _)) hb ha hm).trans (pow_one a)
  rw [he]
  exact ⟨ha,haz,horder,hunique⟩

end NLS.KdV
