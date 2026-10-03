import NLS.ZakharovShabat.SourceBoundaryRootsAnalyticNeighborhood
import NLS.ZakharovShabat.SourceBoundaryRootDifferential

/-! # One complex neighborhood of simple canonical boundary roots

Uniform tail counts give simplicity at all distant signed indices.
Continuity of the moving spectral derivative preserves simplicity in the
finite central block. Both ordinary boundary sequences share one domain.
-/

noncomputable section
open Set Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Original algebraic multiplicity one makes the characteristic derivative
nonzero, without requiring the potential to be real. -/
theorem deriv_periodOneBoundaryCharacteristic_ne_zero_of_multiplicity_one
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition) (φ : CoeffPair p) (z : ℂ)
    (hs : b.algebraicMultiplicity hp (periodOneBoundaryPotential hp hp1 φ).val
      (periodOneBoundaryPotential hp hp1 φ).property z = 1) :
    deriv (periodOneBoundaryCharacteristic hp hp1 b φ) z ≠ 0 := by
  have ha := analyticOnNhd_periodOneBoundaryCharacteristic hp hp1 b φ z (mem_univ _)
  have ho : analyticOrderAt (periodOneBoundaryCharacteristic hp hp1 b φ) z = 1 := by
    rw [analyticOrderAt_periodOneBoundaryCharacteristic,hs]
    rfl
  have hd : analyticOrderAt (deriv (periodOneBoundaryCharacteristic hp hp1 b φ)) z = 0 :=
    analyticOrderAt_deriv_of_pos ha (n := 0) (by simpa using ho)
  intro hzero
  exact (ha.deriv.analyticOrderAt_ne_zero.mpr hzero) hd

/-- At a real source, simplicity of any fixed canonical boundary root
persists on a source neighborhood. -/
theorem eventually_deriv_canonicalBoundaryRoot_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (b : BoundaryCondition)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) :
    ∀ᶠ ψ in 𝓝 φ, deriv (periodOneBoundaryCharacteristic hp hp1 b ψ)
      (canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) ≠ 0 := by
  have hc : Continuous (fun t : ℂ × CoeffPair p =>
      deriv (periodOneBoundaryCharacteristic hp hp1 b t.2) t.1) :=
    continuousOn_univ.mp (continuousOn_spectral_deriv_of_analyticOnNhd
      (fun t : ℂ × CoeffPair p => periodOneBoundaryCharacteristic hp hp1 b t.2 t.1)
      univ isOpen_univ (analyticOnNhd_periodOneBoundaryCharacteristic_joint hp hp1 b))
  have hm := hc.continuousAt.comp
    ((analyticAt_canonicalPeriodOneBoundaryRoots_of_realType hp hp1 b φ hφ n).continuousAt.prodMk continuousAt_id)
  exact hm.eventually_ne (deriv_periodOneBoundaryCharacteristic_at_canonicalRoot_ne_zero_of_realType hp hp1 b φ hφ n)

/-- One neighborhood of each real source supports analytic and simple roots
at every signed index of both ordinary boundary sequences. -/
theorem exists_local_source_allBoundaryRoots_simple
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V, ∀ b : BoundaryCondition, ∀ n : ℤ,
        AnalyticAt ℂ (fun χ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b χ n) ψ ∧
        deriv (periodOneBoundaryCharacteristic hp hp1 b ψ) (canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) ≠ 0 := by
  let F := periodOneBoundaryPotential hp hp1
  obtain ⟨B,hBopen,hφB,hB⟩ := exists_local_source_allBoundaryRoots_analytic hp hp1 φ hφ
  obtain ⟨N,_,U,hUopen,_,hφU,_,_,_,hlabel⟩ := exists_uniform_canonicalBoundaryRoots hp hp1 (F φ)
  obtain ⟨M,A,_,hAopen,_,hφA,_,_,hA⟩ := exists_uniform_analytic_boundaryEigenvalues hp (F φ)
  let K := max N M
  have hcentral : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      ∀ n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        deriv (periodOneBoundaryCharacteristic hp hp1 .dirichlet ψ) (canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet ψ n) ≠ 0 ∧
        deriv (periodOneBoundaryCharacteristic hp hp1 .neumann ψ) (canonicalPeriodOneBoundaryRoots hp hp1 .neumann ψ n) ≠ 0 := by
    rw [Finset.eventually_all]
    intro n _
    exact (eventually_deriv_canonicalBoundaryRoot_ne_zero hp hp1 .dirichlet φ hφ n).and
      (eventually_deriv_canonicalBoundaryRoot_ne_zero hp hp1 .neumann φ hφ n)
  obtain ⟨C,hCsub,hCopen,hφC⟩ := _root_.mem_nhds_iff.mp hcentral
  refine ⟨B ∩ (F ⁻¹' U ∩ (F ⁻¹' A ∩ C)),hBopen.inter ((hUopen.preimage F.continuous).inter
    ((hAopen.preimage F.continuous).inter hCopen)),⟨hφB,hφU,hφA,hφC⟩,?_⟩
  intro ψ hψ b n
  refine ⟨hB b n ψ hψ.1,?_⟩
  by_cases hn : n.natAbs ≤ K
  · have hi : n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by simp only [Finset.mem_Icc]; omega
    have hs := hCsub hψ.2.2.2 n hi
    cases b with
    | dirichlet => exact hs.1
    | neumann => exact hs.2
  · have hN : N < n.natAbs := (le_max_left N M).trans_lt (lt_of_not_ge hn)
    have hM : M < n.natAbs := (le_max_right N M).trans_lt (lt_of_not_ge hn)
    apply deriv_periodOneBoundaryCharacteristic_ne_zero_of_multiplicity_one hp hp1 b ψ
    change b.algebraicMultiplicity hp (F ψ).val (F ψ).property (b.canonicalRoots hp hp1 (F ψ).val (F ψ).property n) = 1
    rw [(hlabel (F ψ) hψ.2.1 b).1.distant n hN]
    exact ((hA b n hM).2 (F ψ) hψ.2.2.1).2

/-- One open complex domain containing every real source has analytic,
simple canonical Dirichlet and Neumann roots at all signed indices. -/
theorem exists_sourceBoundaryRoots_simple_common_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ realTypeSourceLocus p ⊆ W ∧
      ∀ φ ∈ W, ∀ b : BoundaryCondition, ∀ n : ℤ,
        AnalyticAt ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ ∧
        deriv (periodOneBoundaryCharacteristic hp hp1 b φ) (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) ≠ 0 := by
  let S : Set (CoeffPair p) := {φ | ∀ b : BoundaryCondition, ∀ n : ℤ,
    AnalyticAt ℂ (fun ψ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) φ ∧
    deriv (periodOneBoundaryCharacteristic hp hp1 b φ) (canonicalPeriodOneBoundaryRoots hp hp1 b φ n) ≠ 0}
  refine ⟨interior S,isOpen_interior,?_,?_⟩
  · intro φ hφ
    obtain ⟨V,hVopen,hφV,hV⟩ := exists_local_source_allBoundaryRoots_simple hp hp1 φ hφ
    exact mem_interior_iff_mem_nhds.mpr (mem_of_superset (hVopen.mem_nhds hφV) hV)
  · intro φ hφ
    exact interior_subset hφ

end NLS.ZakharovShabat
