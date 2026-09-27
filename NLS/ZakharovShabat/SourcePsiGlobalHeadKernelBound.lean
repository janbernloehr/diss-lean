import NLS.ZakharovShabat.SourcePsiGlobalDistantDeletedRegularFactor

/-!
# Uniform standard-root kernels on finitely many selected circles

The finite nonstandard head of a global psi contour family can be
handled by compactness. Joint analyticity of the selected standard
root makes its inverse locally uniformly bounded on each fixed circle.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- On finitely many selected circles avoiding their base gaps, all
selected standard-root inverses share a local source neighborhood and
a uniform bound. -/
theorem exists_local_sourceStandardRoot_inv_uniformFiniteCircleBound
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ))
    (s : Finset ℤ) (c : ℤ → ℂ) (R : ℤ → ℝ)
    (hcircle : ∀ m : ℤ,
      sphere (c m) (R m) ⊆ sourceCanonicalRootDomain hp hp1 φ) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ ψ ∈ V, ∀ m ∈ s, ∀ z ∈ sphere (c m) (R m),
          ‖(sourceStandardRoot hp hp1 ψ m z)⁻¹‖ ≤ M := by
  obtain ⟨W,hWopen,_,hrealW,hA⟩ :=
    exists_global_source_analytic_midpoint_squaredGap hp hp1
  have hφW : φ ∈ W := hrealW hφ
  obtain ⟨hDopen,_⟩ :=
    sourceCanonicalRootJointProduct_analyticOnNhd_of_symmetric
      hp hp1 W hWopen hA
  let D := sourceCanonicalRootJointDomain hp hp1 W
  have hlocal (m : ℤ) :
      ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
        ∃ M : ℝ, 0 ≤ M ∧
          ∀ ψ ∈ V, ∀ z ∈ sphere (c m) (R m),
            ‖(sourceStandardRoot hp hp1 ψ m z)⁻¹‖ ≤ M := by
    let f : ℂ × CoeffPair p → ℂ := fun t =>
      (sourceStandardRoot hp hp1 t.2 m t.1)⁻¹
    have hf : ContinuousOn f D := by
      intro t ht
      have hroot : AnalyticAt ℂ
          (fun q : ℂ × CoeffPair p =>
            sourceStandardRoot hp hp1 q.2 m q.1) t :=
        sourceStandardRoot_joint_analyticAt_of_symmetric
          hp hp1 t.2 m t.1 (hA t.2 ht.1 m).1
            (hA t.2 ht.1 m).2 (ht.2 m)
      have hzero : sourceStandardRoot hp hp1 t.2 m t.1 ≠ 0 :=
        sourceStandardRoot_ne_zero_off_segment hp hp1 t.2 m t.1 (ht.2 m)
      exact (hroot.inv hzero).continuousAt.continuousWithinAt
    have hbase (z : ℂ) (hz : z ∈ sphere (c m) (R m)) :
        (z,φ) ∈ D := ⟨hφW,hcircle m hz⟩
    obtain ⟨V,hVopen,hφV,M,hM,hbound⟩ :=
      NLS.ComplexAnalysis.exists_local_uniform_bound_on_compact_of_continuousOn
        f D hDopen hf _ (isCompact_sphere _ _) φ hbase
    exact ⟨V,hVopen,hφV,M,hM,fun ψ hψ z hz =>
      (hbound ψ hψ z hz).2⟩
  choose V hVopen hφV M hM hbound using hlocal
  let Vall : Set (CoeffPair p) := ⋂ m ∈ s, V m
  let C : ℝ := ∑ m ∈ s, M m
  have hVallOpen : IsOpen Vall :=
    isOpen_biInter_finset (fun m _ => hVopen m)
  have hφVall : φ ∈ Vall := by
    simp only [Vall,Set.mem_iInter]
    intro m _
    exact hφV m
  have hC : 0 ≤ C := Finset.sum_nonneg (fun m _ => hM m)
  refine ⟨Vall,hVallOpen,hφVall,C,hC,?_⟩
  intro ψ hψ m hm z hz
  simp only [Vall,Set.mem_iInter] at hψ
  have hψm : ψ ∈ V m := hψ m hm
  have hMC : M m ≤ C :=
    Finset.single_le_sum (f := M) (fun k hk => hM k) hm
  exact (hbound m ψ hψm z hz).trans hMC

end NLS.ZakharovShabat
