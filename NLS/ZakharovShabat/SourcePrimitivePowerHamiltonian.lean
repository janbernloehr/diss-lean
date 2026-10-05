import NLS.ZakharovShabat.SourcePrimitivePowerCubicShift
import NLS.ZakharovShabat.SourceFiniteGapContourDecomposition
import NLS.ZakharovShabat.SourceFullAbelianCubicHamiltonianContour

/-! # Lemma 21.2: the finite-gap Hamiltonian identity

The physical Hamiltonian minus its mass and action contributions equals
`-(4/3)` times the sum of actual cubic primitive-power moments. All sums
have finite support at a real finite-gap source.
-/
noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat.SourcePrimitivePowerAtlas
variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (A : SourcePrimitivePowerAtlas hp hp1 W)

/-- Any weighted moment has finite support when the gaps do. -/
theorem weighted_moment_hasSum_of_gap_support (ψ : CoeffPair p) (hψ : ψ ∈ A.domain)
    (S : Finset ℤ)
    (hS : ∀ n ∉ S, canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0)
    (w : ℤ → ℂ) (m : ℕ) :
    HasSum (fun n => w n*A.moment n m ψ) (∑ n ∈ S, w n*A.moment n m ψ) := by
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  rw [A.moment_of_collapsed ψ hψ n (hS n hn) m,mul_zero]

/-- Decompose the actual physical Hamiltonian into its open-gap contributions. -/
theorem finiteGap_hamiltonian_eq_sum (φ : realTypeSourceLocus p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    sourceFiniteGapNLSHamiltonian hp hp1 φ hf 3-2*(sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1)^2 =
      ∑ n ∈ hf.toFinset, ((2*(n:ℂ)*Real.pi)^2*sourceComplexAction hp hp1 n φ.val-
        (4/3:ℂ)*A.moment n 3 φ.val) := by
  classical
  have hφ : φ.val ∈ A.sourceBall φ := mem_ball_self (A.localChart φ).radius_pos
  obtain ⟨D⟩ := (A.localChart φ).charts φ.val hφ
  obtain ⟨T,hT,hdec⟩ := exists_sourceFiniteGap_contour_decomposition hp hp1 φ hf
    (A.localChart φ).center (A.localChart φ).contourRadius ((A.localChart φ).family φ.val hφ)
  obtain ⟨S,_,hH⟩ := exists_sourceFullAbelian_hamiltonian_cube_contour_of_chart φ hf D
  rw [hH (max T S) (le_max_right _ _),hdec (max T S) (le_max_left _ _)
    (fun z => (sourceFullAbelianPrimitive hp hp1 W 0 (z,φ.val))^3)
    (fun z hz => (sourceFullAbelianPrimitive_spectral_analytic D 0 z hz).pow 3)]
  simp_rw [A.unshifted_cubic_circle φ φ.val hφ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [A.moment_one n (A.realType_subset_domain φ.property)]
  have hπ : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- Lemma 21.2, with the actual action sum and the correct negative cubic term. -/
theorem finiteGap_hamiltonian_identity (φ : realTypeSourceLocus p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    sourceFiniteGapNLSHamiltonian hp hp1 φ hf 3-2*(sourceFiniteGapNLSHamiltonian hp hp1 φ hf 1)^2-
      (∑' n : ℤ, (2*(n:ℂ)*Real.pi)^2*sourceComplexAction hp hp1 n φ.val) =
        -(4/3:ℂ)*(∑' n : ℤ, A.moment n 3 φ.val) := by
  classical
  have hφ : φ.val ∈ A.domain := A.realType_subset_domain φ.property
  have hS (n : ℤ) (hn : n ∉ hf.toFinset) :
      canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n = 0 := by
    by_contra hne
    exact hn (hf.mem_toFinset.mpr hne)
  have haction : HasSum (fun n : ℤ => (2*(n:ℂ)*Real.pi)^2*sourceComplexAction hp hp1 n φ.val)
      (∑ n ∈ hf.toFinset, (2*(n:ℂ)*Real.pi)^2*sourceComplexAction hp hp1 n φ.val) := by
    simpa only [A.moment_one _ hφ] using
      A.weighted_moment_hasSum_of_gap_support φ.val hφ hf.toFinset hS
        (fun n => (2*(n:ℂ)*Real.pi)^2) 1
  have hmoment : HasSum (fun n => A.moment n 3 φ.val) (∑ n ∈ hf.toFinset, A.moment n 3 φ.val) := by
    simpa only [one_mul] using
      A.weighted_moment_hasSum_of_gap_support φ.val hφ hf.toFinset hS (fun _ => 1) 3
  rw [A.finiteGap_hamiltonian_eq_sum φ hf,haction.tsum_eq,hmoment.tsum_eq,
    Finset.sum_sub_distrib,← Finset.mul_sum]
  ring

end NLS.ZakharovShabat.SourcePrimitivePowerAtlas
