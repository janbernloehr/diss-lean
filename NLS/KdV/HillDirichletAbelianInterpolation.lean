import NLS.KdV.HillDirichletNumeratorExteriorDecay
import NLS.KdV.HillDirichletSimplicity
import NLS.ComplexAnalysis.SimplePoleInterpolationLimit

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.FunctionalAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The actual normalized Abelian numerator admits its full spectral
interpolation over the simple zeros of the original Dirichlet characteristic.
The finite sums are ordered by expanding energy circles, with every zero included. -/
theorem exists_hillAbelianSelectedGlobalPsi_dirichlet_interpolation :
    ∃ K : ℕ, ∃ s : ℕ → Finset ℂ,
      (∀ k a, a∈s k ↔ a∈closedBall (0 : ℂ) ((centralCircleRadius (k+K))^2) ∧
        hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) a=0) ∧
      (∀ k a, a∈s k → a.im=0 ∧ deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q)) a≠0) ∧
      (∀ n : ℕ, ∀ hn : 1≤n, ∀ E : ℂ,
        hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E≠0 →
        Tendsto (fun k => ∑ a∈s k,
          (hillAbelianSelectedGlobalPsi q hq hr n hn a/
            deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q)) a)/(E-a))
          atTop (𝓝 (hillAbelianSelectedGlobalPsi q hq hr n hn E/
            hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E))) ∧
      ∀ n : ℕ, ∀ hn : 1≤n, ∀ A ε : ℝ, 0<ε →
        ∀ᶠ k : ℕ in atTop, ∀ E : ℂ, ‖E‖≤A →
          hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E≠0 →
          ‖(∑ a∈s k, (hillAbelianSelectedGlobalPsi q hq hr n hn a/
            deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q)) a)/(E-a))-
            hillAbelianSelectedGlobalPsi q hq hr n hn E/
              hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E‖<ε := by
  let p := SpectralWeight.one.toCoeff q
  obtain ⟨K,hK⟩ := exists_hillDirichletCharacteristic_energy_central_bounds ‖p‖
  let R : ℕ → ℝ := fun k => (centralCircleRadius (k+K))^2
  have hR (k : ℕ) : 0<R k := sq_pos_of_pos (centralCircleRadius_pos (k+K))
  have hescape : Tendsto R atTop atTop :=
    tendsto_hillEnergyCircleRadius.comp (tendsto_add_atTop_nat K)
  have hc (k : ℕ) (a : ℂ) (ha : a∈sphere (0 : ℂ) (R k)) : hillL2DirichletCharacteristic p a≠0 :=
    (hK (k+K) (by omega) p le_rfl a ha).1
  obtain ⟨s,hs⟩ := exists_finite_zero_circle_sets (hillL2DirichletCharacteristic p)
    (analyticOnNhd_hillL2DirichletCharacteristic p) R hR hc
  refine ⟨K,s,hs,?_,?_,?_⟩
  · intro k a ha
    have hz := ((hs k a).mp ha).2
    exact ⟨hillL2DirichletCharacteristic_zero_real p hr a hz,
      hillL2DirichletCharacteristic_deriv_ne_zero p hr a hz⟩
  · intro n hn E hE
    apply tendsto_simpleQuotientPrincipalParts_of_circle_decay
      (hillAbelianSelectedGlobalPsi q hq hr n hn) (hillL2DirichletCharacteristic p)
      (analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn)
      (analyticOnNhd_hillL2DirichletCharacteristic p)
      (hillL2DirichletCharacteristic_deriv_ne_zero p hr) R hR hescape hc s hs ?_ E hE
    intro ε hε
    exact (tendsto_add_atTop_nat K).eventually
      (eventually_hillAbelianSelectedGlobalPsi_div_dirichlet_small q hq hr n hn ε hε)
  · intro n hn A ε hε
    apply eventually_simpleQuotientPrincipalParts_error_on_ball
      (hillAbelianSelectedGlobalPsi q hq hr n hn) (hillL2DirichletCharacteristic p)
      (analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn)
      (analyticOnNhd_hillL2DirichletCharacteristic p)
      (hillL2DirichletCharacteristic_deriv_ne_zero p hr) R hR hescape hc s hs ?_ A ε hε
    intro δ hδ
    exact (tendsto_add_atTop_nat K).eventually
      (eventually_hillAbelianSelectedGlobalPsi_div_dirichlet_small q hq hr n hn δ hδ)

end NLS.KdV
