import NLS.KdV.HillDirichletCircleSelection
import NLS.KdV.HillDirichletInterpolationExterior
import NLS.KdV.HillDirichletTerminalVariation
import NLS.ComplexAnalysis.SimplePoleCauchyInterpolation

/-! # Actual positive-index Dirichlet interpolation of normalized numerators -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
namespace NLS.KdV
variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

/-- Literal principal parts at the first N actual positive Dirichlet energies. -/
def hillDirichletInterpolationPrincipalSum (n : ℕ) (hn : 1≤n) (N : ℕ) (w : ℂ) : ℂ :=
  ∑ j∈Finset.range N,
    hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergySequence q hq hr j)/
      deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q)) (hillDirichletEnergySequence q hq hr j)/
        (w-(hillDirichletEnergySequence q hq hr j : ℂ))

/-- The actual filled positive-index interpolation sum retains every
spectral diagonal, including zero energy and collapsed physical gaps. -/
def hillDirichletInterpolationSum (n : ℕ) (hn : 1≤n) (N : ℕ) (w : ℂ) : ℂ :=
  ∑ j∈Finset.range N,
    hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergySequence q hq hr j)*
      hillDirichletGardnerKernel (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) (j+1) (by omega) w

/-- The exact finite interpolation error uses the actual complete
Dirichlet spectrum and the actual characteristic derivative residues. -/
theorem eventually_hillDirichlet_interpolation_cauchy_error (n : ℕ) (hn : 1≤n) :
    ∃ K : ℕ, ∀ N : ℕ, K≤N → ∀ w : ℂ, ‖w‖<(centralCircleRadius N)^2 →
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w≠0 →
      (∮ E in C(0,(centralCircleRadius N)^2), hillAbelianSelectedGlobalPsi q hq hr n hn E/
        hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E/(E-w))=
          (2*Real.pi*I)*(hillAbelianSelectedGlobalPsi q hq hr n hn w/
            hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w-
              hillDirichletInterpolationPrincipalSum q hq hr n hn N w) := by
  classical
  obtain ⟨K,hselect⟩ := eventually_hillDirichlet_sequence_circle_selection q hq hr
  refine ⟨K,?_⟩
  intro N hN w hw hDw
  let μ : ℕ → ℂ := fun j => hillDirichletEnergySequence q hq hr j
  let s := (Finset.range N).image μ
  have hμinj : Function.Injective μ := by
    intro i j he
    exact (strictMono_hillDirichletEnergySequence q hq hr).injective (ofReal_inj.mp he)
  have hs : (s : Set ℂ)⊆ball (0 : ℂ) ((centralCircleRadius N)^2) := by
    intro E hE
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hE
    exact ((hselect N hN).1 j).mpr (Finset.mem_range.mp hj)
  have hzero : ∀ E∈s, hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E=0 := by
    intro E hE
    obtain ⟨j,_hj,rfl⟩ := Finset.mem_image.mp hE
    exact hillDirichletEnergy_zero q hq hr (j+1) (by omega)
  have hsimple : ∀ E∈s, deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q)) E≠0 :=
    fun E hE => hillL2DirichletCharacteristic_deriv_ne_zero _ hr E (hzero E hE)
  have hcover : ∀ E∈closedBall (0 : ℂ) ((centralCircleRadius N)^2),
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E=0 → E∈s := by
    intro E hE hz
    obtain ⟨j,hj,rfl⟩ := ((hselect N hN).2 E hE).mp hz
    exact Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr hj,rfl⟩
  have hsum : simpleQuotientPrincipalParts (hillAbelianSelectedGlobalPsi q hq hr n hn)
      (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q)) s w=
        hillDirichletInterpolationPrincipalSum q hq hr n hn N w := by
    unfold simpleQuotientPrincipalParts
    rw [Finset.sum_image]
    · rfl
    · intro i _hi j _hj he
      exact hμinj he
  rw [← hsum]
  exact circleIntegral_simpleQuotient_cauchy_eq_interpolation_error
    (sq_pos_of_pos (centralCircleRadius_pos N))
    ((analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn).mono (subset_univ _))
    ((analyticOnNhd_hillL2DirichletCharacteristic _).mono (subset_univ _)) s hs hzero hsimple hcover
    (by simpa only [mem_ball,dist_zero_right] using hw) hDw

theorem hillDirichletInterpolationSum_eq_principal (n : ℕ) (hn : 1≤n) (N : ℕ) (w : ℂ)
    (hDw : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w≠0) :
    hillDirichletInterpolationSum q hq hr n hn N w=
      -(hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w)/2*
        hillDirichletInterpolationPrincipalSum q hq hr n hn N w := by
  unfold hillDirichletInterpolationSum hillDirichletInterpolationPrincipalSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  let μ : ℂ := hillDirichletEnergySequence q hq hr j
  have hz : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) μ=0 :=
    hillDirichletEnergy_zero q hq hr (j+1) (by omega)
  have hne : w≠μ := fun he => hDw (he ▸ hz)
  have hd := hillL2DirichletCharacteristic_deriv_ne_zero _ hr μ hz
  change hillAbelianSelectedGlobalPsi q hq hr n hn μ*
    (if w=μ then -1/2 else hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w/
      (2*(μ-w)*deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q)) μ))=
      -hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w/2*
        (hillAbelianSelectedGlobalPsi q hq hr n hn μ/
          deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q)) μ/(w-μ))
  rw [if_neg hne]
  field_simp [hd,sub_ne_zero.mpr hne,sub_ne_zero.mpr (Ne.symm hne)]
  ring

/-- A sufficiently long filled sum has its exact interpolation value
at every actual Dirichlet energy, including collapsed gaps and zero. -/
theorem hillDirichletInterpolationSum_at_dirichlet (n : ℕ) (hn : 1≤n) (N m : ℕ) (hm : m<N) :
    hillDirichletInterpolationSum q hq hr n hn N (hillDirichletEnergySequence q hq hr m)=
      -hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergySequence q hq hr m)/2 := by
  classical
  let μ : ℕ → ℂ := fun j => hillDirichletEnergySequence q hq hr j
  have hz : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) (μ m)=0 :=
    hillDirichletEnergy_zero q hq hr (m+1) (by omega)
  unfold hillDirichletInterpolationSum
  rw [Finset.sum_eq_single m]
  · change hillAbelianSelectedGlobalPsi q hq hr n hn (μ m)*
      (if μ m=μ m then -1/2 else hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) (μ m)/
        (2*(μ m-μ m)*deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q)) (μ m)))=_
    rw [if_pos rfl]
    ring
  · intro j _hj hjm
    have hne : μ m≠μ j := by
      intro he
      exact hjm ((strictMono_hillDirichletEnergySequence q hq hr).injective (ofReal_inj.mp he)).symm
    change hillAbelianSelectedGlobalPsi q hq hr n hn (μ j)*
      (if μ m=μ j then -1/2 else hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) (μ m)/
        (2*(μ j-μ m)*deriv (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q)) (μ j)))=0
    rw [if_neg hne,hz,zero_div,mul_zero]
  · intro h
    exact False.elim (h (Finset.mem_range.mpr hm))

private theorem eventually_norm_lt_energyCircle (w : ℂ) :
    ∀ᶠ N : ℕ in atTop, ‖w‖<(centralCircleRadius N)^2 := by
  obtain ⟨M,hM⟩ := exists_nat_gt ((‖w‖+1)/Real.pi)
  filter_upwards [eventually_ge_atTop M] with N hN
  have h1 : ‖w‖+1<(M : ℝ)*Real.pi := (div_lt_iff₀ Real.pi_pos).mp hM
  have h2 : (M : ℝ)≤N := by exact_mod_cast hN
  have hc : ‖w‖+1<centralCircleRadius N := by
    unfold centralCircleRadius
    nlinarith [Real.pi_pos]
  nlinarith [norm_nonneg w]

theorem tendsto_hillDirichlet_outerCauchy (n : ℕ) (hn : 1≤n) (w : ℂ) :
    Tendsto (fun N : ℕ => ∮ E in C(0,(centralCircleRadius N)^2),
      hillAbelianSelectedGlobalPsi q hq hr n hn E/
        hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E/(E-w)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K,hK⟩ := eventually_hillDirichlet_outerCauchy_small q hq hr n hn ‖w‖ (norm_nonneg w) hε
  filter_upwards [eventually_ge_atTop K] with N hN
  simpa only [dist_zero_right] using hK N hN w le_rfl

/-- The positive-index interpolation sums converge at every complex
spectral value. Their diagonal values are genuinely filled, not total
zero-over-zero values of unfilled principal parts. -/
theorem tendsto_hillDirichletInterpolationSum (n : ℕ) (hn : 1≤n) (w : ℂ) :
    Tendsto (fun N : ℕ => hillDirichletInterpolationSum q hq hr n hn N w) atTop
      (𝓝 (-hillAbelianSelectedGlobalPsi q hq hr n hn w/2)) := by
  by_cases hz : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w=0
  · obtain ⟨m,rfl⟩ := (hillL2DirichletCharacteristic_zero_iff_sequence q hq hr w).mp hz
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (m+1)] with N hN
    exact (hillDirichletInterpolationSum_at_dirichlet q hq hr n hn N m (by omega)).symm
  · obtain ⟨K,hK⟩ := eventually_hillDirichlet_interpolation_cauchy_error q hq hr n hn
    let O : ℕ → ℂ := fun N => ∮ E in C(0,(centralCircleRadius N)^2),
      hillAbelianSelectedGlobalPsi q hq hr n hn E/
        hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E/(E-w)
    let A : ℂ := 2*Real.pi*I
    have hA : A≠0 := by dsimp only [A];exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
    have he : (fun N : ℕ => hillDirichletInterpolationSum q hq hr n hn N w)=ᶠ[atTop]
        (fun N => -hillAbelianSelectedGlobalPsi q hq hr n hn w/2+
          hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w/(2*A)*O N) := by
      filter_upwards [eventually_ge_atTop K,eventually_norm_lt_energyCircle w] with N hN hw
      have hc := hK N hN w hw hz
      rw [hillDirichletInterpolationSum_eq_principal q hq hr n hn N w hz]
      change -(hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w)/2*
        hillDirichletInterpolationPrincipalSum q hq hr n hn N w=_
      change O N=A*(hillAbelianSelectedGlobalPsi q hq hr n hn w/
        hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w-
          hillDirichletInterpolationPrincipalSum q hq hr n hn N w) at hc
      rw [hc]
      field_simp [hz,hA]
      ring
    have hO : Tendsto O atTop (𝓝 0) := tendsto_hillDirichlet_outerCauchy q hq hr n hn w
    have ht : Tendsto (fun N => -hillAbelianSelectedGlobalPsi q hq hr n hn w/2+
        hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w/(2*A)*O N) atTop
        (𝓝 (-hillAbelianSelectedGlobalPsi q hq hr n hn w/2)) := by
      simpa only [mul_zero,add_zero] using
        (tendsto_const_nhds.add (tendsto_const_nhds.mul hO))
    exact ht.congr' he.symm

/-- The actual characteristic-weighted Cauchy error identity holds on
whole evaluation discs, including the filled Dirichlet diagonals. -/
theorem eventually_hillDirichlet_filled_interpolation_error (n : ℕ) (hn : 1≤n) :
    ∃ K : ℕ, ∀ N : ℕ, K≤N → ∀ w : ℂ, ‖w‖<(centralCircleRadius N)^2 →
      (2*Real.pi*I)*(hillDirichletInterpolationSum q hq hr n hn N w+
        hillAbelianSelectedGlobalPsi q hq hr n hn w/2)=
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w/2*
        (∮ E in C(0,(centralCircleRadius N)^2), hillAbelianSelectedGlobalPsi q hq hr n hn E/
          hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E/(E-w)) := by
  obtain ⟨K₀,hK₀⟩ := eventually_hillDirichlet_interpolation_cauchy_error q hq hr n hn
  obtain ⟨K₁,hK₁⟩ := eventually_hillDirichlet_sequence_circle_selection q hq hr
  refine ⟨max K₀ K₁,?_⟩
  intro N hN w hw
  by_cases hz : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w=0
  · have hwc : w∈closedBall (0 : ℂ) ((centralCircleRadius N)^2) := by
      simpa only [mem_closedBall,dist_zero_right] using hw.le
    obtain ⟨m,hm,he⟩ := ((hK₁ N ((le_max_right _ _).trans hN)).2 w hwc).mp hz
    have hs : hillDirichletInterpolationSum q hq hr n hn N w=-hillAbelianSelectedGlobalPsi q hq hr n hn w/2 := by
      rw [he]
      exact hillDirichletInterpolationSum_at_dirichlet q hq hr n hn N m hm
    rw [hs,hz,zero_div,zero_mul]
    ring
  · rw [hillDirichletInterpolationSum_eq_principal q hq hr n hn N w hz,
      hK₀ N ((le_max_left _ _).trans hN) w hw hz]
    field_simp [hz]
    ring

/-- The actual positive-index interpolation converges uniformly on
every bounded energy disc, retaining all filled Dirichlet diagonals. -/
theorem tendstoUniformlyOn_hillDirichletInterpolationSum (n : ℕ) (hn : 1≤n) (L : ℝ) (hL : 0≤L) :
    TendstoUniformlyOn (fun N : ℕ => fun w : ℂ => hillDirichletInterpolationSum q hq hr n hn N w)
      (fun w => -hillAbelianSelectedGlobalPsi q hq hr n hn w/2) atTop (closedBall (0 : ℂ) L) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hc : Continuous (hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q)) :=
    (analyticOnNhd_hillL2DirichletCharacteristic _).continuous
  obtain ⟨M,hM,hMb⟩ := ((isCompact_closedBall (0 : ℂ) L).image hc).isBounded.exists_pos_norm_le
  obtain ⟨K₀,hK₀⟩ := eventually_hillDirichlet_filled_interpolation_error q hq hr n hn
  obtain ⟨K₁,hK₁⟩ := eventually_hillDirichlet_outerCauchy_small q hq hr n hn L hL (div_pos hε hM)
  have hcircle : ∀ᶠ N : ℕ in atTop, L<(centralCircleRadius N)^2 := by
    have hh := eventually_norm_lt_energyCircle (L : ℂ)
    simpa only [norm_real,Real.norm_of_nonneg hL] using hh
  filter_upwards [eventually_ge_atTop K₀,eventually_ge_atTop K₁,hcircle] with N hN₀ hN₁ hR
  intro w hw
  have hwL : ‖w‖≤L := by simpa only [mem_closedBall,dist_zero_right] using hw
  have he := hK₀ N hN₀ w (hwL.trans_lt hR)
  have ho := hK₁ N hN₁ w hwL
  have hD : ‖hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) w‖≤M := hMb _ ⟨w,hw,rfl⟩
  have hnorm : ‖(2*Real.pi*I : ℂ)‖=2*Real.pi := by
    simp only [norm_mul,norm_ofNat,norm_real,Real.norm_of_nonneg Real.pi_pos.le,norm_I,mul_one]
  have heq := congrArg norm he
  rw [norm_mul,hnorm,norm_mul,norm_div,norm_ofNat] at heq
  have hprod := mul_le_mul_of_nonneg_right hD
    (norm_nonneg (∮ E in C(0,(centralCircleRadius N)^2), hillAbelianSelectedGlobalPsi q hq hr n hn E/
      hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) E/(E-w)))
  have hb : ‖hillDirichletInterpolationSum q hq hr n hn N w+hillAbelianSelectedGlobalPsi q hq hr n hn w/2‖<ε := by
    have ho' := (lt_div_iff₀ hM).mp ho
    have hm := le_mul_of_one_le_left
      (norm_nonneg (hillDirichletInterpolationSum q hq hr n hn N w+hillAbelianSelectedGlobalPsi q hq hr n hn w/2))
      (show (1 : ℝ)≤4*Real.pi by nlinarith [Real.pi_gt_three])
    nlinarith
  rw [dist_comm,dist_eq_norm]
  convert hb using 1
  congr 1
  ring

end NLS.KdV
