import NLS.KdV.HillDirichletVelocityCoordinate

/-! # Finite-gap reduction of actual coordinate velocities

Closed gaps remove their actual coordinate-velocity terms. No evaluation
of the remaining finite spectral sum as a Hamiltonian frequency is assumed.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillDirichletVelocityCoordinateTerm_eq_zero_of_closed
    (n k : ℕ) (hn : 1≤n) (hk : 1≤k)
    (hc : hillRealGapHalfLength q hq hr k=0) (K : ℂ) :
    (hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr k hk)*K)*
      (I*hillDirichletAbelianCoordinate q hq hr n hn)=0 := by
  by_cases hkn : k=n
  · subst k
    rw [hillDirichletAbelianCoordinate_closed q hq hr n hn hc]
    simp only [mul_zero]
  · rw [hillAbelianSelectedGlobalPsi_dirichlet_eq_zero_of_closed q hq hr n k hn hk hkn hc]
    simp only [zero_mul]

theorem eventually_hillDirichletVelocityCoordinateSum_eq_finite
    (n : ℕ) (hn : 1≤n) (K : ℕ → ℂ) (N : ℕ)
    (hclosed : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q hq hr k=0) :
    ∀ᶠ M : ℕ in atTop,
      (∑ j ∈ Finset.range M,
        hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr (j+1) (by omega))*K (j+1))*
          (I*hillDirichletAbelianCoordinate q hq hr n hn)=
      (∑ j ∈ Finset.range N,
        hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr (j+1) (by omega))*K (j+1))*
          (I*hillDirichletAbelianCoordinate q hq hr n hn) := by
  filter_upwards [eventually_ge_atTop N] with M hM
  rw [Finset.sum_mul,Finset.sum_mul]
  symm
  apply Finset.sum_subset (Finset.range_mono hM)
  intro j _hjM hjN
  have hNj : N≤j := by simpa only [Finset.mem_range,not_lt] using hjN
  exact hillDirichletVelocityCoordinateTerm_eq_zero_of_closed q hq hr n (j+1) hn (by omega)
    (hclosed (j+1) (by omega) (by omega)) (K (j+1))

variable (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

theorem fderiv_hillDirichletAbelianCoordinate_finite_gap_velocity
    (n : ℕ) (hn : 1≤n) (C : Coeff 2 → ℂ)
    (hC : DifferentiableAt ℂ C (SpectralWeight.one.toCoeff q))
    (hmatch : ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
      C (SpectralWeight.one.toCoeff p.val)=hillDirichletAbelianCoordinate p.val p.property.1 p.property.2 n hn)
    (V : Coeff 2) (K : ℕ → ℂ)
    (hv : ∀ (k : ℕ) (hk : 1≤k), HillDirichletVelocityData (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) k hk V (K k))
    (N : ℕ) (hclosed : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q hq hr k=0) :
    (fderiv ℂ C (SpectralWeight.one.toCoeff q)) V=
      (∑ j ∈ Finset.range N,
        hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr (j+1) (by omega))*K (j+1))*
          (I*hillDirichletAbelianCoordinate q hq hr n hn) := by
  have hlim := fderiv_hillDirichletAbelianCoordinate_velocity_extension q hq hr h0q h0r n hn C hC hmatch V K hv
  have hfinite := eventually_hillDirichletVelocityCoordinateSum_eq_finite q hq hr n hn K N hclosed
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hfinite.mono (fun _ h => h.symm)))

end NLS.KdV
