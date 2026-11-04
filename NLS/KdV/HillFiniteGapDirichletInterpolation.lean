import NLS.KdV.HillDirichletInterpolation
import NLS.KdV.HillGardnerOpenCorrection
import NLS.KdV.HillFiniteGapExterior

/-! # Exact finite-gap Dirichlet partial fractions

The actual numerator divided by the actual Dirichlet characteristic is a
finite principal-part sum. Include the own index even if its gap is closed;
its numerator need not vanish there.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- Actual finite-gap potentials supply a finite cutoff that includes the
selected index even if that selected gap is closed. -/
theorem HillFiniteGap.exists_dirichlet_cutoff (hfg : HillFiniteGap q hq hr) (n : ℕ) :
    ∃ N : ℕ, n≤N ∧ ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q hq hr k=0 := by
  obtain ⟨K,hK⟩ := HillFiniteGap.exists_collapsed_tail q hq hr hfg
  refine ⟨max n K,le_max_left _ _,?_⟩
  intro k hk hNk
  have he := hK k (by omega) hk
  simp only [hillRealGapHalfLength,he,sub_self,zero_div]

theorem eventually_hillDirichletInterpolationSum_eq_finite
    (n N : ℕ) (hn : 1≤n) (hnN : n≤N)
    (hclosed : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q hq hr k=0) :
    ∀ᶠ M : ℕ in atTop, ∀ w : ℂ,
      hillDirichletInterpolationSum q hq hr n hn M w=
        hillDirichletInterpolationSum q hq hr n hn N w := by
  filter_upwards [eventually_ge_atTop N] with M hM
  intro w
  unfold hillDirichletInterpolationSum
  symm
  apply Finset.sum_subset (Finset.range_mono hM)
  intro j _hjM hjN
  have hNj : N≤j := by simpa only [Finset.mem_range,not_lt] using hjN
  have hkn : j+1≠n := by omega
  change hillAbelianSelectedGlobalPsi q hq hr n hn
    (hillDirichletEnergy q hq hr (j+1) (by omega))*_=0
  rw [hillAbelianSelectedGlobalPsi_dirichlet_eq_zero_of_closed q hq hr n (j+1) hn (by omega)
    hkn (hclosed (j+1) (by omega) (by omega)),zero_mul]

/-- Exact filled interpolation, simultaneously at every complex energy,
including Dirichlet energies and a closed own gap. -/
theorem hillDirichletInterpolationSum_finite_gap
    (n N : ℕ) (hn : 1≤n) (hnN : n≤N)
    (hclosed : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q hq hr k=0) (w : ℂ) :
    hillDirichletInterpolationSum q hq hr n hn N w=
      -hillAbelianSelectedGlobalPsi q hq hr n hn w/2 := by
  have he := eventually_hillDirichletInterpolationSum_eq_finite q hq hr n N hn hnN hclosed
  have hfinite : Tendsto (fun M => hillDirichletInterpolationSum q hq hr n hn M w) atTop
      (𝓝 (hillDirichletInterpolationSum q hq hr n hn N w)) :=
    tendsto_const_nhds.congr' (he.mono (fun _ h => (h w).symm))
  exact tendsto_nhds_unique hfinite (tendsto_hillDirichletInterpolationSum q hq hr n hn w)

/-- Actual finite principal parts, with no assumed Dirichlet product
formula and no prescribed normalized leading constant. -/
theorem hillAbelianSelectedGlobalPsi_div_dirichlet_finite_gap
    (n N : ℕ) (hn : 1≤n) (hnN : n≤N)
    (hclosed : ∀ (k : ℕ) (_hk : 1≤k), N<k → hillRealGapHalfLength q hq hr k=0)
    (w : ℂ) (hDw : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w≠0) :
    hillAbelianSelectedGlobalPsi q hq hr n hn w/
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w=
        hillDirichletInterpolationPrincipalSum q hq hr n hn N w := by
  have he := hillDirichletInterpolationSum_finite_gap q hq hr n N hn hnN hclosed w
  rw [hillDirichletInterpolationSum_eq_principal q hq hr n hn N w hDw] at he
  apply (div_eq_iff hDw).mpr
  linear_combination 2*he

end NLS.KdV
