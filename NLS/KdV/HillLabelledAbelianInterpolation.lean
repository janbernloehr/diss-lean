import NLS.KdV.HillDirichletPoleIdentification
import NLS.KdV.HillDirichletNumeratorExteriorDecay
import NLS.ComplexAnalysis.SimplePoleInterpolationLimit

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- The genuine normalized Abelian interpolation is the ordinary
sequence of partial sums over the original gap-labelled Dirichlet data,
with uniform remainder on every bounded set of non-pole energies. -/
theorem hillAbelianSelectedGlobalPsi_dirichlet_labelled_interpolation
    (n : ℕ) (hn : 1≤n) :
    (∀ E : ℂ, hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E≠0 →
      Tendsto (fun k => ∑ j∈Finset.range k,
        (hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr (j+1) (by omega))/
          deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q))
            (hillDirichletEnergy q hq hr (j+1) (by omega)))/
          (E-(hillDirichletEnergy q hq hr (j+1) (by omega) : ℂ)))
        atTop (𝓝 (hillAbelianSelectedGlobalPsi q hq hr n hn E/
          hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E))) ∧
    ∀ A ε : ℝ, 0<ε → ∀ᶠ k : ℕ in atTop, ∀ E : ℂ, ‖E‖≤A →
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E≠0 →
      ‖(∑ j∈Finset.range k,
        (hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr (j+1) (by omega))/
          deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q))
            (hillDirichletEnergy q hq hr (j+1) (by omega)))/
          (E-(hillDirichletEnergy q hq hr (j+1) (by omega) : ℂ)))-
        hillAbelianSelectedGlobalPsi q hq hr n hn E/
          hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E‖<ε := by
  let p := SpectralWeight.one.toCoeff q
  let μ : ℕ → ℂ := fun j => hillDirichletEnergy q hq hr (j+1) (by omega)
  let f := hillAbelianSelectedGlobalPsi q hq hr n hn
  let g := hillL2DirichletCharacteristic p
  obtain ⟨Ke,hKe⟩ := exists_hillDirichletCharacteristic_central_label_exhaustion q hq hr
  obtain ⟨Kg,hKg⟩ := exists_hillDirichletEnergy_central_containment q hq hr
  let K := max Ke Kg
  let R : ℕ → ℝ := fun k => (centralCircleRadius (k+K))^2
  let s : ℕ → Finset ℂ := fun k => (Finset.range (k+K)).image μ
  have hR (k : ℕ) : 0<R k := sq_pos_of_pos (centralCircleRadius_pos (k+K))
  have hescape : Tendsto R atTop atTop :=
    tendsto_hillEnergyCircleRadius.comp (tendsto_add_atTop_nat K)
  have hc (k : ℕ) (E : ℂ) (hE : E∈sphere (0 : ℂ) (R k)) : g E≠0 :=
    (hKe (k+K) (by dsimp only [K];omega)).1 E hE
  have hs (k : ℕ) (E : ℂ) : E∈s k ↔ E∈closedBall (0 : ℂ) (R k) ∧ g E=0 := by
    constructor
    · intro hE
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hE
      exact ⟨ball_subset_closedBall (hKg (k+K) (by dsimp only [K];omega) j (Finset.mem_range.mp hj)),
        hillDirichletEnergy_zero q hq hr (j+1) (by omega)⟩
    · rintro ⟨hE,hzero⟩
      obtain ⟨j,hj,hμ⟩ := ((hKe (k+K) (by dsimp only [K];omega)).2 E hE).mp hzero
      exact Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr hj,hμ.symm⟩
  have hinj : Function.Injective μ := by
    intro i j hij
    exact (strictMono_hillDirichletEnergy_sequence q hq hr).injective (Complex.ofReal_injective hij)
  have hsum (k : ℕ) (E : ℂ) : simpleQuotientPrincipalParts f g (s k) E=
      ∑ j∈Finset.range (k+K), (f (μ j)/deriv g (μ j))/(E-μ j) := by
    rw [simpleQuotientPrincipalParts,Finset.sum_image]
    exact fun a _ b _ he => hinj he
  have hsmall (ε : ℝ) (hε : 0<ε) : ∀ᶠ k : ℕ in atTop,
      ∀ E∈sphere (0 : ℂ) (R k), ‖f E/g E‖≤ε :=
    (tendsto_add_atTop_nat K).eventually
      (eventually_hillAbelianSelectedGlobalPsi_div_dirichlet_small q hq hr n hn ε hε)
  have hf := analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn
  have hg := analyticOnNhd_hillL2DirichletCharacteristic p
  have hsimple := hillL2DirichletCharacteristic_deriv_ne_zero p hr
  constructor
  · intro E hE
    apply (tendsto_add_atTop_iff_nat K).mp
    have ht := tendsto_simpleQuotientPrincipalParts_of_circle_decay f g hf hg hsimple
      R hR hescape hc s hs hsmall E hE
    simp_rw [hsum] at ht
    exact ht
  · intro A ε hε
    have hu := eventually_simpleQuotientPrincipalParts_error_on_ball f g hf hg hsimple
      R hR hescape hc s hs hsmall A ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp hu
    filter_upwards [eventually_ge_atTop (N+K)] with k hk E hEA hE
    have hh := hN (k-K) (by omega) E hEA hE
    rw [hsum,Nat.sub_add_cancel (by omega : K≤k)] at hh
    exact hh

end NLS.KdV
