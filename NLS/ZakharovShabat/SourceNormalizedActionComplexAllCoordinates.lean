import NLS.ZakharovShabat.SourceNormalizedActionComplexSequenceSpace

/-!
# One complex source neighborhood for all normalized-action coordinates

The distant normalized-action coordinates are differentiable on one
common neighborhood. Each of the remaining finitely many coordinates
has its own neighborhood; their finite intersection gives a common
complex domain for every index. Intersecting with the sequence-space
neighborhood also gives a uniform `ℓq` bound for the deviation.
-/

noncomputable section
open Set Metric Complex Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every normalized-action coordinate is complex differentiable on
one open source neighborhood of a real-type potential. -/
theorem exists_local_sourceNormalizedActionComplexExtension_allCoordinates_differentiableOn
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ n : ℤ,
        DifferentiableOn ℂ (sourceNormalizedActionComplexExtension hp hp1 n) V := by
  obtain ⟨K,Vt,hVtopen,hφVt,htail⟩ :=
    exists_local_sourceNormalizedActionComplexExtension_differentiableOn_tail
      hp hp1 φ hreal
  let s := Finset.Icc (-(K:ℤ)) (K:ℤ)
  let U (n : ℤ) : Set (CoeffPair p) :=
    Classical.choose (exists_local_sourceNormalizedActionComplexExtension_differentiableOn
      hp hp1 φ hreal n)
  have hU (n : ℤ) : IsOpen (U n) ∧ φ ∈ U n ∧
      DifferentiableOn ℂ (sourceNormalizedActionComplexExtension hp hp1 n) (U n) := by
    have hs := Classical.choose_spec
      (exists_local_sourceNormalizedActionComplexExtension_differentiableOn
        hp hp1 φ hreal n)
    exact ⟨hs.1,hs.2.1,hs.2.2.1⟩
  let Vf : Set (CoeffPair p) := ⋂ n ∈ s, U n
  have hVfopen : IsOpen Vf := isOpen_biInter_finset (fun n _ => (hU n).1)
  have hφVf : φ ∈ Vf := by
    simp only [Vf,Set.mem_iInter]
    intro n _
    exact (hU n).2.1
  let V := Vt ∩ Vf
  refine ⟨V,hVtopen.inter hVfopen,⟨hφVt,hφVf⟩,?_⟩
  intro n
  by_cases hn : K ≤ n.natAbs
  · exact (htail n hn).mono inter_subset_left
  · have hns : n ∈ s := by
      simp only [s,Finset.mem_Icc]
      omega
    apply (hU n).2.2.mono
    intro ψ hψ
    have hψVf : ψ ∈ Vf := hψ.2
    simp only [Vf,Set.mem_iInter] at hψVf
    exact hψVf n hns

/-- On one complex source neighborhood, every coordinate is
differentiable and the full normalized-action deviation has a
uniformly bounded `ℓq` realization. -/
theorem exists_local_sourceNormalizedActionComplexExtension_allCoordinates_boundedCoeff
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ M : ℝ,
        (∀ n : ℤ,
          DifferentiableOn ℂ (sourceNormalizedActionComplexExtension hp hp1 n) V) ∧
        (∀ ψ ∈ V, ∃ A : Coeff q,
          (∀ n : ℤ, A n = sourceNormalizedActionDeviation hp hp1 ψ n) ∧
          ‖A‖ ≤ M) := by
  obtain ⟨Vd,hVdopen,hφVd,hdiff⟩ :=
    exists_local_sourceNormalizedActionComplexExtension_allCoordinates_differentiableOn
      hp hp1 φ hreal
  obtain ⟨Vb,hVbopen,hφVb,M,hbound⟩ :=
    exists_local_sourceNormalizedActionDeviation_coeff_uniformNorm
      hp hp1 hq1 hq hhalf φ hreal
  let V := Vd ∩ Vb
  refine ⟨V,hVdopen.inter hVbopen,⟨hφVd,hφVb⟩,M,?_,?_⟩
  · intro n
    exact (hdiff n).mono inter_subset_left
  · intro ψ hψ
    exact hbound ψ hψ.2

/-- The normalized-action deviation defines a locally bounded map into
`ℓq` whose scalar coordinates are complex differentiable on the same
complex source neighborhood. -/
theorem exists_local_sourceNormalizedActionDeviation_boundedMap
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ M : ℝ, ∃ F : V → Coeff q,
        (∀ ψ : V, ∀ n : ℤ,
          F ψ n = sourceNormalizedActionDeviation hp hp1 ψ.1 n) ∧
        (∀ ψ : V, ‖F ψ‖ ≤ M) ∧
        (∀ n : ℤ,
          DifferentiableOn ℂ (sourceNormalizedActionComplexExtension hp hp1 n) V) := by
  obtain ⟨V,hVopen,hφV,M,hdiff,hbound⟩ :=
    exists_local_sourceNormalizedActionComplexExtension_allCoordinates_boundedCoeff
      hp hp1 hq1 hq hhalf φ hreal
  let F : V → Coeff q := fun ψ => Classical.choose (hbound ψ.1 ψ.2)
  refine ⟨V,hVopen,hφV,M,F,?_,?_,hdiff⟩
  · intro ψ n
    exact (Classical.choose_spec (hbound ψ.1 ψ.2)).1 n
  · intro ψ
    exact (Classical.choose_spec (hbound ψ.1 ψ.2)).2

end NLS.ZakharovShabat
