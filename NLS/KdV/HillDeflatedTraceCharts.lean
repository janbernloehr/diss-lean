import NLS.KdV.HillDeflatedGapPhysicalMatching
import NLS.ComplexAnalysis.JointSpectralDerivativeAnalytic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

def hillDeflatedTraceNumerator (n : ℕ) (z : ℂ) : ℂ :=
  deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z / hillDeflatedEnergyCanonicalRoot q hq hr n z

def hillLocalDeflatedTraceNumerator (n : ℕ) (t : ℂ × Coeff 2) : ℂ :=
  deriv (hillL2Discriminant t.2) t.1 / hillLocalDeflatedComplexRoot q hq hr n t

theorem analyticOnNhd_hillDeflatedTraceNumerator (n : ℕ) (hn : 1 ≤ n) :
    AnalyticOnNhd ℂ (hillDeflatedTraceNumerator q hq hr n) (hillGapFilledDomain q hq hr n) := by
  intro z hz
  exact ((analyticOnNhd_hillL2Discriminant (SpectralWeight.one.toCoeff q)).deriv z (mem_univ _)).div
    (analyticOnNhd_hillDeflatedEnergyCanonicalRoot q hq hr n z hz)
    (hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr n hn z hz)

theorem analyticOnNhd_hillLocalDeflatedTraceNumerator (n : ℕ) (hn : 1 ≤ n) :
    AnalyticOnNhd ℂ (hillLocalDeflatedTraceNumerator q hq hr n) (hillLocalDeflatedRootDomain q hq hr n) := by
  have hD := analyticOnNhd_spectral_deriv_of_analyticOnNhd
    (fun t : ℂ × Coeff 2 => hillL2Discriminant t.2 t.1) univ isOpen_univ analyticOnNhd_hillL2Discriminant_joint
  intro t ht
  exact (hD t (mem_univ _)).div (analyticOnNhd_hillLocalDeflatedComplexRoot q hq hr n hn t ht)
    (hillLocalDeflatedComplexRoot_ne_zero q hq hr n hn t ht)

theorem exists_hillLocalDeflatedTraceNumerator_physical_neighborhood (n : ℕ) (hn : 1 ≤ n) :
    ∃ E : Set ℂ, ∃ V : Set RealPeriodOneHillPotential, IsOpen E ∧ IsOpen V ∧
      segment ℝ (hillRealLabels q hq hr (2*n-1) : ℂ) (hillRealLabels q hq hr (2*n) : ℂ) ⊆ E ∧
      (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) ∈ V ∧
      ∀ p ∈ V, ∀ z ∈ E,
        (z,SpectralWeight.one.toCoeff p.val) ∈ hillLocalDeflatedRootDomain q hq hr n ∧
        z ∈ hillGapFilledDomain p.val p.property.1 p.property.2 n ∧
        hillLocalDeflatedTraceNumerator q hq hr n (z,SpectralWeight.one.toCoeff p.val) =
          hillDeflatedTraceNumerator p.val p.property.1 p.property.2 n z := by
  obtain ⟨E,V,hE,hV,hgap,hqV,hmatch⟩ := exists_hillLocalDeflatedComplexRoot_gap_physical_matching q hq hr n hn
  refine ⟨E,V,hE,hV,hgap,hqV,?_⟩
  intro p hp z hz
  have h := hmatch p hp z hz
  refine ⟨h.1,h.2.1,?_⟩
  simp only [hillLocalDeflatedTraceNumerator,hillDeflatedTraceNumerator,h.2.2]

end NLS.KdV
