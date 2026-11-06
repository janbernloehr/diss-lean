import NLS.KdV.HillRegularIndexedPrimitives
import NLS.KdV.HillClosedGapAbelianCorrections

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
include h0q h0r

/-- Actual analytic physical primitive germs whose finite-sum indexed-source
derivatives stabilize at half the selected normalized numerator. -/
theorem exists_hillPhysicalPrimitive_partial_sum_indexed_variations
    (n : ℕ) (hn : 1≤n)
    (hreg : ∀ j : ℕ, hillDirichletSheetRoot (SpectralWeight.one.toCoeff q)
      (hillDirichletEnergy q hq hr (j+1) (by omega))≠0) :
    ∃ B ε : ℕ → Coeff 2 → ℂ, ∃ e : ℕ → ℂ,
      (∀ j : ℕ,
        AnalyticAt ℂ (B j) (SpectralWeight.one.toCoeff q) ∧
        AnalyticAt ℂ (ε j) (SpectralWeight.one.toCoeff q) ∧
        ε j (SpectralWeight.one.toCoeff q)=e j ∧
        e j∈segment ℝ (-(Real.pi : ℂ)) (Real.pi : ℂ) ∧
        ∀ᶠ p : RealPeriodOneHillPotential in 𝓝 (⟨q,hq,hr⟩ : RealPeriodOneHillPotential),
          cosineGapPoint (hillRealGapCenter p.val p.property.1 p.property.2 (j+1))
            (hillRealGapHalfLength p.val p.property.1 p.property.2 (j+1)) (ε j (SpectralWeight.one.toCoeff p.val))=
              (hillDirichletEnergy p.val p.property.1 p.property.2 (j+1) (by omega) : ℂ) ∧
          Complex.sin (ε j (SpectralWeight.one.toCoeff p.val))=hillDirichletGapSine p.val p.property.1 p.property.2 (j+1) (by omega) ∧
          B j (SpectralWeight.one.toCoeff p.val)=hillAbelianCosinePrimitive p.val p.property.1 p.property.2 n hn (j+1)
            (ε j (SpectralWeight.one.toCoeff p.val))) ∧
      ∀ k : ℕ, ∀ hk : 1≤k,
        Tendsto (fun N => (fderiv ℂ (fun p : Coeff 2 => ∑ j∈Finset.range N,B j p) (SpectralWeight.one.toCoeff q))
          (SpectralWeight.one.toCoeff (hillIndexedDiscriminantHamiltonianSource (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) k hk)))
          atTop (𝓝 (hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr k hk)/2)) := by
  have hgap (j : ℕ) : hillRealGapHalfLength q hq hr (j+1)≠0 := by
    intro hz
    exact hreg j (hillDirichletSheetRoot_eq_zero_of_halfLength_zero q hq hr (j+1) (by omega) hz)
  choose B ε e hB hε hε0 he hphysical hder using
    (fun j : ℕ => exists_hillDirichletPrimitive_regular_indexed_source_variations q hq hr h0q h0r
      n (j+1) hn (by omega) (hgap j) (hreg j))
  refine ⟨B,ε,e,?_,?_⟩
  · intro j
    refine ⟨hB j,hε j,hε0 j,he j,?_⟩
    filter_upwards [hphysical j] with p hp
    exact ⟨hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2.1⟩
  · intro k hk
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop k] with K hK
    symm
    rw [fderiv_fun_sum (u := Finset.range K) (fun j _ => (hB j).differentiableAt)]
    simp only [sum_apply]
    have hterm (j : ℕ) :
        (fderiv ℂ (B j) (SpectralWeight.one.toCoeff q))
          (SpectralWeight.one.toCoeff (hillIndexedDiscriminantHamiltonianSource
            (⟨q,hq,hr⟩ : RealPeriodOneHillPotential) k hk))=
          if j=k-1 then hillAbelianSelectedGlobalPsi q hq hr n hn (hillDirichletEnergy q hq hr k hk)/2 else 0 := by
      rw [hder j k hk]
      by_cases hj : j=k-1
      · have hjk : j+1=k := by omega
        simp only [hjk,if_true,if_pos hj]
      · have hjk : j+1≠k := by omega
        rw [if_neg hjk,if_neg hj]
    simp only [hterm]
    have hmem : k-1∈Finset.range K := Finset.mem_range.mpr (by omega)
    simp only [Finset.sum_ite_eq',if_pos hmem]

end NLS.KdV
