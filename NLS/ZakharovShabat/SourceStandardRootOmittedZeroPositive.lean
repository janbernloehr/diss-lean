import NLS.ZakharovShabat.SourceStandardRootNormalizedFactorSign
import NLS.ZakharovShabat.RealDeletedPeriodicProduct

/-!
# Positive omitted standard-root product on the central real gap

For index zero every retained normalized root factor is positive:
negative indices lie before the gap and have negative denominators,
while positive indices lie after it and have positive denominators.
The finite cutoffs are positive and their nonzero limit is positive.
-/

noncomputable section
open Set Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every normalized factor retained after omitting index zero is
strictly positive and real on an open central real gap. -/
theorem sourceStandardRoot_normalized_re_pos_on_zeroGap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    {m : ℤ} (hm : m ≠ 0) {x : ℝ}
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) 0).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) 0).re) :
    0 < (sourceStandardRoot hp hp1 ψ m (x:ℂ) /
      singleSpectralDenominator m).re := by
  rcases lt_or_gt_of_ne hm with hneg | hpos
  · exact sourceStandardRoot_normalized_re_pos_of_neg_before
      hp hp1 ψ hreal hneg hneg hx
  · exact sourceStandardRoot_normalized_re_pos_of_nonneg_after
      hp hp1 ψ hreal hpos.le hpos hx

/-- Every finite symmetric cutoff of the central omitted product is
strictly positive on the open real central gap. -/
theorem sourceStandardRootOmittedPartialProduct_re_pos_on_zeroGap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (N : ℕ) (x : ℝ)
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) 0).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) 0).re) :
    0 < (sourceStandardRootOmittedPartialProduct
      hp hp1 0 N ((x:ℂ),ψ)).re := by
  let s : Finset ℤ := (Finset.Icc (-(N:ℤ)) (N:ℤ)).erase 0
  let f (m : ℤ) : ℂ := sourceStandardRoot hp hp1 ψ m (x:ℂ) /
    singleSpectralDenominator m
  have hrealFactor (m : ℤ) (hm : m ∈ s) : f m = ((f m).re:ℂ) := by
    have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm).1
    have him : (f m).im = 0 := by
      have hr := sourceStandardRoot_im_eq_zero_off_selected_realGap
        hp hp1 ψ hreal hm0 hx
      have hd : (singleSpectralDenominator m).im = 0 := by
        unfold singleSpectralDenominator
        split_ifs <;> simp
      dsimp [f]
      simp [Complex.div_im,hr,hd]
    apply Complex.ext
    · rfl
    · exact him
  have hprod : (∏ m ∈ s, f m) = ((∏ m ∈ s, (f m).re):ℂ) := by
    apply Finset.prod_congr rfl
    intro m hm
    exact hrealFactor m hm
  have hpos : 0 < ∏ m ∈ s, (f m).re := by
    apply Finset.prod_pos
    intro m hm
    exact sourceStandardRoot_normalized_re_pos_on_zeroGap
      hp hp1 ψ hreal (Finset.mem_erase.mp hm).1 hx
  change 0 < ((∏ m ∈ s, f m) / singleSpectralDenominator 0).re
  simp only [singleSpectralDenominator, if_pos, div_one]
  rw [hprod]
  exact_mod_cast hpos

/-- On the open central real gap, the infinite omitted standard-root
product has strictly positive real value. -/
theorem sourceStandardRootOmittedProduct_re_pos_on_zeroGap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (x : ℝ)
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) 0).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) 0).re) :
    0 < (sourceStandardRootOmittedProduct hp hp1 0 ψ (x:ℂ)).re := by
  let P := sourceStandardRootOmittedProduct hp hp1 0 ψ (x:ℂ)
  have ht := tendsto_sourceStandardRootOmittedPartialProduct
    hp hp1 0 ψ (x:ℂ)
  have htre : Tendsto
      (fun N : ℕ => (sourceStandardRootOmittedPartialProduct
        hp hp1 0 N ((x:ℂ),ψ)).re) atTop (𝓝 P.re) :=
    continuous_re.continuousAt.tendsto.comp ht
  have hnonneg : 0 ≤ P.re :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds htre
      (fun N => (sourceStandardRootOmittedPartialProduct_re_pos_on_zeroGap
        hp hp1 ψ hreal N x hx).le)
  have hIm : P.im = 0 :=
    sourceStandardRootOmittedProduct_im_eq_zero_on_realGap
      hp hp1 ψ hreal 0 x hx
  obtain ⟨W,_,_,hWreal,hdisjoint⟩ :=
    exists_global_source_disjoint_periodicSegments hp hp1
  have hψW : ψ ∈ W := hWreal hreal
  have hxseg : (x:ℂ) ∈ sourcePeriodicSegment hp hp1 ψ 0 :=
    sourcePeriodicSegment_mem_of_realIcc hp hp1 ψ hreal 0 x
      ⟨hx.1.le,hx.2.le⟩
  have hdomain : (x:ℂ) ∈ sourceStandardRootOmittedDomain hp hp1 ψ 0 := by
    intro m hm hmem
    exact Set.disjoint_left.mp (hdisjoint ψ hψW 0 m (Ne.symm hm)) hxseg hmem
  have hne : P ≠ 0 :=
    sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ (x:ℂ) 0 hdomain
  by_contra hnot
  have hzero : P.re = 0 := le_antisymm (le_of_not_gt hnot) hnonneg
  apply hne
  apply Complex.ext
  · exact hzero
  · exact hIm

end NLS.ZakharovShabat
