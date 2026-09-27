import NLS.ZakharovShabat.SourceNormalizedActionComplexSequenceSpace
import NLS.SequenceSpaces.TwoExponentDecomposition

/-!
# Exact two-exponent normalized-action asymptotics

The uniform complex-source majorants for the normalized-action
deviation are converted to an exact sum of an `ℓq` sequence and an
`ℓ^(p/2)` sequence. The finitely many central coordinates are absorbed
by the `ℓq` component. Both components have locally uniform norm
bounds, including when `p/2 < 1`.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)]

/-- On one complex source neighborhood, the full normalized-action
deviation equals an `ℓq` sequence plus an `ℓ^(p/2)` sequence with
separate uniform norm bounds. -/
theorem exists_local_sourceNormalizedActionDeviation_twoExponentDecomposition
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (hhalf : ENNReal.ofReal (p.toReal/2) ≤ q)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ Lq Lg : ℝ, ∀ ψ ∈ V,
        ∃ Aq : Coeff q, ∃ Ag : Coeff (ENNReal.ofReal (p.toReal/2)),
          (∀ n : ℤ,
            Aq n+Ag n = sourceNormalizedActionDeviation hp hp1 ψ n) ∧
          ‖Aq‖ ≤ Lq ∧ ‖Ag‖ ≤ Lg := by
  obtain ⟨Vm,hVmopen,hφVm,K,Lq,Lg,hmajor⟩ :=
    exists_local_sourceNormalizedActionComplexExtension_complex_uniformSequenceMajorants
      hp hp1 hq1 hq hhalf φ hreal
  obtain ⟨Vf,hVfopen,hφVf,M,hfull⟩ :=
    exists_local_sourceNormalizedActionDeviation_coeff_uniformNorm
      hp hp1 hq1 hq hhalf φ hreal
  have hpr : 0 < p.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans hp1)) hp
  have hr : 0 < ENNReal.ofReal (p.toReal/2) :=
    ENNReal.ofReal_pos.mpr (half_pos hpr)
  let V := Vm ∩ Vf
  refine ⟨V,hVmopen.inter hVfopen,⟨hφVm,hφVf⟩,Lq+M,Lg,?_⟩
  intro ψ hψ
  obtain ⟨Cq,Cg,hpoint,hCq,hCg⟩ := hmajor ψ hψ.1
  obtain ⟨A,hA,hAnorm⟩ := hfull ψ hψ.2
  obtain ⟨Aq,Ag,hdecomp,hAq,hAg⟩ :=
    Coeff.exists_coeff_decomposition_of_tailMajorants hr A K Cq Cg (by
      intro n hn
      rw [hA n]
      exact hpoint n hn)
  refine ⟨Aq,Ag,?_,?_,hAg.trans hCg⟩
  · intro n
    rw [← hA n]
    exact hdecomp n
  · exact hAq.trans (add_le_add hCq hAnorm)

/-- For every finite exponent `q > 1`, the normalized-action
deviation is locally uniformly an exact `ℓq + ℓ^(p/2)` sum. When
`q < p/2`, the full deviation already belongs to `ℓ^(p/2)`, so its
`ℓq` summand can be zero. -/
theorem exists_local_sourceNormalizedActionDeviation_twoExponentDecomposition_allQ
    [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (hq : q ≠ ⊤)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ Lq Lg : ℝ, ∀ ψ ∈ V,
        ∃ Aq : Coeff q, ∃ Ag : Coeff (ENNReal.ofReal (p.toReal/2)),
          (∀ n : ℤ,
            Aq n+Ag n = sourceNormalizedActionDeviation hp hp1 ψ n) ∧
          ‖Aq‖ ≤ Lq ∧ ‖Ag‖ ≤ Lg := by
  let r := ENNReal.ofReal (p.toReal/2)
  by_cases hrq : r ≤ q
  · exact exists_local_sourceNormalizedActionDeviation_twoExponentDecomposition
      hp hp1 hq1 hq hrq φ hreal
  · have hqr : q < r := lt_of_not_ge hrq
    have hr1 : 1 < r := hq1.trans hqr
    have hrTop : r ≠ ⊤ := by simp [r]
    letI : Fact (1 ≤ r) := ⟨hr1.le⟩
    obtain ⟨V,hVopen,hφV,M,hfull⟩ :=
      exists_local_sourceNormalizedActionDeviation_coeff_uniformNorm
        (p := p) (q := r) hp hp1 hr1 hrTop le_rfl φ hreal
    refine ⟨V,hVopen,hφV,0,M,?_⟩
    intro ψ hψ
    obtain ⟨Ag,hAg,hAgnorm⟩ := hfull ψ hψ
    refine ⟨0,Ag,?_,by simp,hAgnorm⟩
    intro n
    simpa only [lp.coeFn_zero,Pi.zero_apply,zero_add] using hAg n

end NLS.ZakharovShabat
