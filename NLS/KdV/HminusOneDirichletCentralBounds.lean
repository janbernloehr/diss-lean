import NLS.KdV.HminusOneDirichletCentralCounting

/-! Uniform complex native Dirichlet central counts on the ORIGINAL H^-1
potential neighborhoods, with explicit bounds on all enclosed energies. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
namespace NLS.KdV

/-- Every squared central frequency has an explicit energy bound, independent
of the potential or its multiplicity. -/
theorem norm_square_sub_le_of_mem_centralSpectralBox (N : ℕ) (c z : ℂ)
    (hz : z ∈ centralSpectralBox N) :
    ‖z^2-c‖ ≤ ((N:ℝ)*Real.pi+Real.pi/2+N)^2+‖c‖ := by
  have hb : 0 ≤ (N:ℝ)*Real.pi+Real.pi/2+N := by positivity
  have hn : ‖z‖ ≤ (N:ℝ)*Real.pi+Real.pi/2+N := by
    exact (Complex.norm_le_abs_re_add_abs_im z).trans
      (add_le_add hz.1.le hz.2)
  calc
    _ ≤ ‖z^2‖+‖c‖ := norm_sub_le _ _
    _ = ‖z‖^2+‖c‖ := by rw [norm_pow]
    _ ≤ _ := add_le_add ((sq_le_sq₀ (norm_nonneg _) hb).mpr hn) le_rfl

/-- Every actual central native eigenvalue obeys the same explicit norm bound. -/
theorem norm_le_of_mem_hillHminusDirichletCentralSpectrum
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (hi : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c))
    (N : ℕ) (e : ℂ) (he : e ∈ hillHminusDirichletCentralSpectrum q u c N) :
    ‖e‖ ≤ ((N:ℝ)*Real.pi+Real.pi/2+N)^2+‖c‖ := by
  obtain ⟨_,z,hz,rfl⟩ := (mem_hillHminusDirichletCentralSpectrum q u c hi N e).mp he
  exact norm_square_sub_le_of_mem_centralSpectralBox N c z hz

/-- ONE fixed local Miura chart and ONE original H^-1 neighborhood support
the exact actual central algebraic count at EVERY larger cutoff.
The neighborhood is chosen before the varying potential and cutoff. -/
theorem HillHminusMiuraChart.exists_uniform_dirichletCentralCount
    (C : HillHminusMiuraChart) (q : PeriodOneHminusOne) (hq : q ∈ C.domain) :
    ∃ N₀ : ℕ, ∃ V : Set PeriodOneHminusOne,
      0 < N₀ ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ C.domain ∧
      ∀ a ∈ V, ∀ N : ℕ, N₀ ≤ N →
        (∑ e ∈ hillHminusDirichletCentralSpectrum a (C.lift a) C.energyShift N,
          singularDirichletAlgebraicMultiplicity (periodOneOriginal a) e) = N := by
  let F : PeriodOneHminusOne → CoeffPair 2 := fun a => hillMiuraDiagonal (C.lift a)
  have hF : AnalyticOnNhd ℂ F C.domain := by
    intro a ha
    exact (hillMiuraDiagonal.analyticAt _).comp (C.lift_analytic a ha)
  obtain ⟨N₀,U,hN,hU,_,hqU,_,hc⟩ := exists_uniform_auxiliaryPeriodOneCountingData
    (by simp) (by norm_num) (F q)
  let V := C.domain ∩ F ⁻¹' U
  refine ⟨N₀,V,hN,hF.continuousOn.isOpen_inter_preimage C.domain_open hU,
    ⟨hq,hqU⟩,inter_subset_left,?_⟩
  intro a ha N hNa
  exact sum_hillHminusDirichletCentralSpectrum_multiplicity a (C.lift a)
    C.energyShift (C.image a ha.1) N (hc (F a) ha.2 N hNa)

/-- Every complex original unit-period H^-1 source admits a common neighborhood,
fixed cutoff and uniform bound for ALL actual central eigenvalues, while their
full native algebraic multiplicities sum to precisely that cutoff. -/
theorem exists_uniform_hillHminusDirichletCentralSpectrum_bound (q : PeriodOneHminusOne) :
    ∃ C : HillHminusMiuraChart, ∃ N : ℕ, ∃ V : Set PeriodOneHminusOne, ∃ R : ℝ,
      0 < N ∧ IsOpen V ∧ q ∈ V ∧ V ⊆ C.domain ∧ 0 ≤ R ∧
      ∀ a ∈ V,
        (∑ e ∈ hillHminusDirichletCentralSpectrum a (C.lift a) C.energyShift N,
          singularDirichletAlgebraicMultiplicity (periodOneOriginal a) e) = N ∧
        ∀ e ∈ hillHminusDirichletCentralSpectrum a (C.lift a) C.energyShift N, ‖e‖ ≤ R := by
  let C := hillHminusMiuraChartAt q
  obtain ⟨N,V,hN,hV,hq,hsub,hcount⟩ :=
    C.exists_uniform_dirichletCentralCount q (mem_hillHminusMiuraChartAt q)
  refine ⟨C,N,V,((N:ℝ)*Real.pi+Real.pi/2+N)^2+‖C.energyShift‖,
    hN,hV,hq,hsub,by positivity,?_⟩
  intro a ha
  exact ⟨hcount a ha N le_rfl,fun e he =>
    norm_le_of_mem_hillHminusDirichletCentralSpectrum a (C.lift a) C.energyShift
      (C.image a (hsub ha)) N e he⟩

end NLS.KdV
