import NLS.KdV.HminusOneDirichletAuxiliaryMultiplicity
import NLS.ComplexAnalysis.SymmetricSquareCount
import NLS.ZakharovShabat.AuxiliaryCounting

/-! Actual COMPLEX native Dirichlet central counts, including the ramified
zero frequency. All central energies and algebraic multiplicities are
constructed from the full operators rather than a supplied root list. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped BigOperators Classical
namespace NLS.KdV

/-- The actual finite auxiliary central spectrum of a complex diagonal lift. -/
def hillMiuraDirichletCentralFrequencies (u : Coeff 2) (N : ℕ) : Finset ℂ :=
  BoundaryCondition.auxiliaryCentralSpectrum .dirichlet (by simp)
    (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).val
    (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).property N

theorem mem_hillMiuraDirichletCentralFrequencies (u : Coeff 2) (N : ℕ) (z : ℂ) :
    z ∈ hillMiuraDirichletCentralFrequencies u N ↔
      auxiliaryPeriodOneCharacteristic (by simp) (by norm_num) .dirichlet
        (hillMiuraDiagonal u) z = 0 ∧ z ∈ centralSpectralBox N := by
  rw [hillMiuraDirichletCentralFrequencies,BoundaryCondition.mem_auxiliaryCentralSpectrum,
    auxiliaryPeriodOneCharacteristic_eq_zero_iff]

/-- The normalization factor always supplies zero to the auxiliary central set. -/
theorem zero_mem_hillMiuraDirichletCentralFrequencies (u : Coeff 2) (N : ℕ) :
    0 ∈ hillMiuraDirichletCentralFrequencies u N := by
  rw [mem_hillMiuraDirichletCentralFrequencies]
  constructor
  · rw [auxiliaryDirichlet_eq_mul_quasiHillL2Dirichlet,zero_mul]
  · change |(0:ℂ).re| < (N:ℝ)*Real.pi+Real.pi/2 ∧ |(0:ℂ).im| ≤ (N:ℝ)
    simp only [Complex.zero_re,Complex.zero_im,abs_zero]
    constructor
    · positivity
    · positivity

/-- The entire complex auxiliary central cluster is reflection invariant. -/
theorem neg_mem_hillMiuraDirichletCentralFrequencies (u : Coeff 2) (N : ℕ)
    (z : ℂ) (hz : z ∈ hillMiuraDirichletCentralFrequencies u N) :
    -z ∈ hillMiuraDirichletCentralFrequencies u N := by
  rw [mem_hillMiuraDirichletCentralFrequencies] at hz ⊢
  constructor
  · rw [auxiliaryDirichlet_hillMiuraDiagonal_neg,hz.1,neg_zero]
  · simpa only [centralSpectralBox,mem_ofPred_eq,Complex.neg_re,Complex.neg_im,
      abs_neg] using hz.2

/-- Actual native scalar spectral values in the squared auxiliary central region.
The spurious shifted-zero energy is removed whenever it is not a native eigenvalue. -/
def hillHminusDirichletCentralSpectrum (q : PeriodOneHminusOne) (u : Coeff 2)
    (c : ℂ) (N : ℕ) : Finset ℂ :=
  ((hillMiuraDirichletCentralFrequencies u N).image (fun z => z^2-c)).filter
    (fun e => e ∈ singularDirichletSpectrum (periodOneOriginal q))

/-- This finite set is EXACTLY the native spectrum in the squared central region. -/
theorem mem_hillHminusDirichletCentralSpectrum
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (hi : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) (N : ℕ) (e : ℂ) :
    e ∈ hillHminusDirichletCentralSpectrum q u c N ↔
      e ∈ singularDirichletSpectrum (periodOneOriginal q) ∧
        e ∈ (fun z : ℂ => z^2-c) '' centralSpectralBox N := by
  classical
  simp only [hillHminusDirichletCentralSpectrum,Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨z,hz,he⟩,hs⟩
    exact ⟨hs,z,((mem_hillMiuraDirichletCentralFrequencies u N z).mp hz).2,he⟩
  · rintro ⟨hs,z,hz,rfl⟩
    refine ⟨⟨z,?_,rfl⟩,hs⟩
    rw [mem_hillMiuraDirichletCentralFrequencies]
    refine ⟨?_,hz⟩
    rw [auxiliaryDirichlet_eq_mul_hillHminusDirichlet q u c z hi,
      (mem_singularDirichletSpectrum_source_iff q _).mp hs,mul_zero]

/-- An auxiliary central count 2N+1 gives EXACTLY N actual scalar Dirichlet
eigenvalues counted with full native algebraic multiplicity. The proof includes
all possible shifted-zero scalar multiplicities and complex associated vectors. -/
theorem sum_hillHminusDirichletCentralSpectrum_multiplicity
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (hi : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) (N : ℕ)
    (hcount : AuxiliaryCountingData (by simp)
      (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).val
      (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).property N) :
    (∑ e ∈ hillHminusDirichletCentralSpectrum q u c N,
      singularDirichletAlgebraicMultiplicity (periodOneOriginal q) e) = N := by
  classical
  let a : ℂ → ℕ := BoundaryCondition.auxiliaryAlgebraicMultiplicity .dirichlet (by simp)
    (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).val
    (auxiliaryPeriodOnePotential (by simp) (by norm_num) (hillMiuraDiagonal u)).property
  let m := singularDirichletAlgebraicMultiplicity (periodOneOriginal q)
  let K := hillMiuraDirichletCentralFrequencies u N
  have hsum := NLS.ComplexAnalysis.sum_symmetric_square_multiplicity K c a m
    (zero_mem_hillMiuraDirichletCentralFrequencies u N)
    (neg_mem_hillMiuraDirichletCentralFrequencies u N)
    (auxiliaryDirichletMultiplicity_zero_eq_one_add_twice q u c hi)
    (fun z _ hz => auxiliaryDirichletMultiplicity_eq_native_of_ne_zero q u c z hi hz)
  have haux : (∑ z ∈ K, a z) = 2*N+1 := hcount.central_multiplicity .dirichlet
  have himage : (∑ e ∈ K.image (fun z => z^2-c), m e) = N := by omega
  change (∑ e ∈ (K.image (fun z => z^2-c)).filter
    (fun e => e ∈ singularDirichletSpectrum (periodOneOriginal q)), m e) = N
  rw [Finset.sum_filter]
  calc
    _ = ∑ e ∈ K.image (fun z => z^2-c), m e := by
      apply Finset.sum_congr rfl
      intro e _
      split_ifs with he
      · rfl
      · have hm : m e = 0 := Nat.eq_zero_of_not_pos fun hp =>
          he ((singularDirichletAlgebraicMultiplicity_pos_iff (periodOneOriginal q) e).mp hp)
        exact hm.symm
    _ = N := himage

/-- For every complex lift, the exact central native multiplicity count holds
at EVERY sufficiently large cutoff. No central label or count is assumed. -/
theorem exists_hillHminusDirichletCentralSpectrum_count
    (q : PeriodOneHminusOne) (u : Coeff 2) (c : ℂ)
    (hi : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (∑ e ∈ hillHminusDirichletCentralSpectrum q u c N,
        singularDirichletAlgebraicMultiplicity (periodOneOriginal q) e) = N := by
  obtain ⟨N₀,U,hN,_,_,hu,_,hc⟩ := exists_uniform_auxiliaryPeriodOneCountingData
    (by simp) (by norm_num) (hillMiuraDiagonal u)
  exact ⟨N₀,hN,fun N h => sum_hillHminusDirichletCentralSpectrum_multiplicity
    q u c hi N (hc _ hu N h)⟩

end NLS.KdV
