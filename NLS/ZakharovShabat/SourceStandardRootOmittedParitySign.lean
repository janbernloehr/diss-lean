import NLS.ZakharovShabat.SourceStandardRootOmittedFiniteParity
import NLS.ZakharovShabat.SourceStandardRootOmittedZeroPositive

/-!
# Parity sign of the infinite omitted-root product

The finite symmetric cutoffs have a common sign once they include
the omitted index. Their limit has the same weak sign; nonvanishing
on the open selected gap makes the sign strict.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At every open real-type gap, the real omitted standard-root
product has the sign determined by the absolute index parity. -/
theorem sourceStandardRootOmittedProduct_signed_re_pos_on_realGap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (x : ℝ)
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    0 < (-1:ℝ)^n.natAbs *
      (sourceStandardRootOmittedProduct hp hp1 n ψ (x:ℂ)).re := by
  by_cases hn : n = 0
  · subst n
    simpa using sourceStandardRootOmittedProduct_re_pos_on_zeroGap
      hp hp1 ψ hreal x hx
  let P := sourceStandardRootOmittedProduct hp hp1 n ψ (x:ℂ)
  have ht := tendsto_sourceStandardRootOmittedPartialProduct
    hp hp1 n ψ (x:ℂ)
  have htre : Tendsto
      (fun N : ℕ => (sourceStandardRootOmittedPartialProduct
        hp hp1 n N ((x:ℂ),ψ)).re) atTop (𝓝 P.re) :=
    continuous_re.continuousAt.tendsto.comp ht
  have htsigned : Tendsto
      (fun N : ℕ => (-1:ℝ)^n.natAbs *
        (sourceStandardRootOmittedPartialProduct
          hp hp1 n N ((x:ℂ),ψ)).re) atTop
      (𝓝 ((-1:ℝ)^n.natAbs * P.re)) :=
    tendsto_const_nhds.mul htre
  have hnonneg : 0 ≤ (-1:ℝ)^n.natAbs * P.re :=
    le_of_tendsto_of_tendsto tendsto_const_nhds htsigned (by
      filter_upwards [eventually_ge_atTop n.natAbs] with N hN
      exact (sourceStandardRootOmittedPartialProduct_signed_re_pos
        hp hp1 ψ hreal hn N hN hx).le)
  have hIm : P.im = 0 :=
    sourceStandardRootOmittedProduct_im_eq_zero_on_realGap
      hp hp1 ψ hreal n x hx
  obtain ⟨W,_,_,hWreal,hdisjoint⟩ :=
    exists_global_source_disjoint_periodicSegments hp hp1
  have hψW : ψ ∈ W := hWreal hreal
  have hxseg : (x:ℂ) ∈ sourcePeriodicSegment hp hp1 ψ n :=
    sourcePeriodicSegment_mem_of_realIcc hp hp1 ψ hreal n x
      ⟨hx.1.le,hx.2.le⟩
  have hdomain : (x:ℂ) ∈ sourceStandardRootOmittedDomain hp hp1 ψ n := by
    intro m hm hmem
    exact Set.disjoint_left.mp (hdisjoint ψ hψW n m (Ne.symm hm)) hxseg hmem
  have hne : P ≠ 0 :=
    sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ (x:ℂ) n hdomain
  have hrealne : P.re ≠ 0 := by
    intro hre
    apply hne
    apply Complex.ext
    · exact hre
    · exact hIm
  have hsignedne : (-1:ℝ)^n.natAbs * P.re ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) hrealne
  exact lt_of_le_of_ne hnonneg (Ne.symm hsignedne)

end NLS.ZakharovShabat
