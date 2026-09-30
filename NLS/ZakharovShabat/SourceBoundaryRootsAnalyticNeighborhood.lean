import NLS.ZakharovShabat.CanonicalPeriodOneBoundaryAnalytic

/-!
# A common source domain for analytic boundary coordinates

The distant canonical coordinates agree with analytic contour traces on one
uniform labeling neighborhood. The remaining two finite blocks are analytic
near each real source by algebraic simplicity. Intersecting these finitely
many neighborhoods gives one neighborhood for every index of both sequences.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A single complex source neighborhood supports analyticity of every
Dirichlet and Neumann coordinate, including all central indices. -/
theorem exists_local_source_allBoundaryRoots_analytic
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ b : BoundaryCondition, ∀ n : ℤ,
        AnalyticOnNhd ℂ (fun ψ : CoeffPair p =>
          canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) V := by
  let F := periodOneBoundaryPotential hp hp1
  obtain ⟨N,_,U,hUopen,_,hφU,_,_,_,hlabel⟩ :=
    exists_uniform_canonicalBoundaryRoots hp hp1 (F φ)
  obtain ⟨M,A,_,hAopen,_,hφA,_,_,hA⟩ :=
    exists_uniform_analytic_boundaryEigenvalues hp (F φ)
  let K := max N M
  have hcentral : ∀ᶠ ψ : CoeffPair p in 𝓝 φ,
      ∀ n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        AnalyticAt ℂ (fun χ : CoeffPair p =>
          canonicalPeriodOneBoundaryRoots hp hp1 .dirichlet χ n) ψ ∧
        AnalyticAt ℂ (fun χ : CoeffPair p =>
          canonicalPeriodOneBoundaryRoots hp hp1 .neumann χ n) ψ := by
    rw [Finset.eventually_all]
    intro n _
    have hd := (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType
      hp hp1 .dirichlet φ hφ n).eventually_analyticAt
    have hn := (analyticAt_canonicalPeriodOneBoundaryRoots_of_realType
      hp hp1 .neumann φ hφ n).eventually_analyticAt
    exact hd.and hn
  obtain ⟨C,hCsub,hCopen,hφC⟩ := _root_.mem_nhds_iff.mp hcentral
  let V := F ⁻¹' U ∩ (F ⁻¹' A ∩ C)
  have hVopen : IsOpen V := (hUopen.preimage F.continuous).inter
    ((hAopen.preimage F.continuous).inter hCopen)
  refine ⟨V,hVopen,⟨hφU,hφA,hφC⟩,?_⟩
  intro b n ψ hψ
  by_cases hn : n.natAbs ≤ K
  · have hindex : n ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
      simp only [Finset.mem_Icc]
      omega
    have hc := hCsub hψ.2.2 n hindex
    cases b with
    | dirichlet => exact hc.1
    | neumann => exact hc.2
  · have hNK : N < n.natAbs := (le_max_left N M).trans_lt (lt_of_not_ge hn)
    have hMK : M < n.natAbs := (le_max_right N M).trans_lt (lt_of_not_ge hn)
    have ht : AnalyticAt ℂ (fun χ : CoeffPair p => b.eigenvalue hp (F χ).val n) ψ :=
      AnalyticAt.comp (g := fun χ : dirichletSubspace (p := p) =>
        b.eigenvalue hp χ.val n) (f := F) (x := ψ)
        ((hA b n hMK).1 (F ψ) hψ.2.1) (F.analyticAt ψ)
    apply ht.congr
    have hnear : ∀ᶠ χ : CoeffPair p in 𝓝 ψ, F χ ∈ U :=
      F.continuous.continuousAt.eventually (hUopen.mem_nhds hψ.1)
    filter_upwards [hnear] with χ hχ
    exact ((hlabel (F χ) hχ b).1.distant n hNK).symm

/-- One open complex neighborhood of all real sources supports both entire
indexed sequences of canonical ordinary boundary coordinates. -/
theorem exists_sourceBoundaryRoots_analytic_common_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧
      {φ | IsRealType (CoeffPair.toMax p φ)} ⊆ W ∧
      ∀ b : BoundaryCondition, ∀ n : ℤ,
        AnalyticOnNhd ℂ (fun ψ : CoeffPair p =>
          canonicalPeriodOneBoundaryRoots hp hp1 b ψ n) W := by
  let S : Set (CoeffPair p) := {ψ | ∀ b : BoundaryCondition, ∀ n : ℤ,
    AnalyticAt ℂ (fun χ : CoeffPair p => canonicalPeriodOneBoundaryRoots hp hp1 b χ n) ψ}
  refine ⟨interior S,isOpen_interior,?_,?_⟩
  · intro φ hφ
    obtain ⟨V,hVopen,hφV,hV⟩ := exists_local_source_allBoundaryRoots_analytic hp hp1 φ hφ
    apply mem_interior_iff_mem_nhds.mpr
    exact mem_of_superset (hVopen.mem_nhds hφV) (fun ψ hψ b n => hV b n ψ hψ)
  · intro b n ψ hψ
    exact interior_subset hψ b n

end NLS.ZakharovShabat
