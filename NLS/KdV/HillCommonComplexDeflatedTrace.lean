import NLS.ComplexAnalysis.JointSpectralDerivativeAnalytic
import NLS.KdV.HillFilledFreeGapRoot
import NLS.KdV.HillFilledFreeGapPhysical
import NLS.KdV.HillDeflatedTraceCharts

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

def hillComplexDeflatedTraceNumerator (k : ℕ) (t : ℂ × Coeff 2) : ℂ :=
  deriv (hillL2Discriminant t.2) t.1/hillFilledFreeGapRoot h0q h0r k t

theorem exists_hillComplexDeflatedTraceNumerator_common_analytic (B : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ k : ℕ, N≤k →
      AnalyticOnNhd ℂ (hillComplexDeflatedTraceNumerator h0q h0r k)
        (closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
          (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) ×ˢ ball (0 : Coeff 2) B) := by
  obtain ⟨N,hN,hroot⟩ := exists_hillFilledFreeGapRoot_bounded_complex_analytic h0q h0r B
  refine ⟨N,hN,?_⟩
  intro k hk t ht
  have hd := analyticOnNhd_spectral_deriv_of_analyticOnNhd
    (fun x : ℂ × Coeff 2 => hillL2Discriminant x.2 x.1) univ isOpen_univ analyticOnNhd_hillL2Discriminant_joint
  exact (hd t (mem_univ _)).div ((hroot k hk).1 t ht) (((hroot k hk).2 t.2 ht.2 t.1 ht.1).2.1)

theorem exists_hillComplexDeflatedTraceNumerator_bounded_real_physical_matching (B : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ q : WeightedCoeff SpectralWeight.one.toWeight 2,
      ∀ hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0,
      ∀ hr : IsRealHillPotential (SpectralWeight.one.toCoeff q), ‖SpectralWeight.one.toCoeff q‖≤B →
        ∀ k : ℕ, N≤k → ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
          (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
          hillComplexDeflatedTraceNumerator h0q h0r k (E,SpectralWeight.one.toCoeff q)=
            hillDeflatedTraceNumerator q hq hr k E := by
  obtain ⟨N,hN,hroot⟩ := exists_hillFilledFreeGapRoot_bounded_real_physical_matching h0q h0r B
  refine ⟨N,hN,?_⟩
  intro q hq hr hp k hk E hE
  rw [hillComplexDeflatedTraceNumerator,hillDeflatedTraceNumerator,hroot q hq hr hp k hk E hE]

end NLS.KdV
