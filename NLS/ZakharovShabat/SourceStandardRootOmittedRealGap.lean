import NLS.ZakharovShabat.SourceStandardRootRealExteriorSign
import NLS.ZakharovShabat.SourceStandardRootOmittedProduct

/-!
# Reality of the omitted standard-root product on a real gap

Every factor retained when the selected root is omitted is real at
an interior point of that gap. The finite symmetric products are
therefore real, and pointwise convergence carries reality to the
canonical omitted product.
-/

noncomputable section
open Set Filter Topology Complex ComplexConjugate
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every symmetric finite cutoff of the omitted standard-root
product is real at an interior point of a real-type gap. -/
theorem sourceStandardRootOmittedPartialProduct_im_eq_zero_on_realGap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (N : ℕ) (x : ℝ)
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    (sourceStandardRootOmittedPartialProduct hp hp1 n N ((x:ℂ),ψ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  have hden (m : ℤ) : conj (singleSpectralDenominator m) =
      singleSpectralDenominator m := by
    unfold singleSpectralDenominator
    split_ifs <;> simp
  have hfactor (m : ℤ) (hm : m ≠ n) :
      conj (sourceStandardRoot hp hp1 ψ m (x:ℂ) /
        singleSpectralDenominator m) =
        sourceStandardRoot hp hp1 ψ m (x:ℂ) /
          singleSpectralDenominator m := by
    rw [map_div₀, hden]
    rw [Complex.conj_eq_iff_im.mpr
      (sourceStandardRoot_im_eq_zero_off_selected_realGap
        hp hp1 ψ hreal hm hx)]
  unfold sourceStandardRootOmittedPartialProduct
  rw [map_div₀, map_prod, hden]
  congr 1
  apply Finset.prod_congr rfl
  intro m hm
  exact hfactor m (Finset.mem_erase.mp hm).1

/-- The infinite omitted standard-root product is real throughout
the interior of the selected real-type gap. -/
theorem sourceStandardRootOmittedProduct_im_eq_zero_on_realGap
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) (x : ℝ)
    (hx : x ∈ Ioo
      (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re) :
    (sourceStandardRootOmittedProduct hp hp1 n ψ (x:ℂ)).im = 0 := by
  have ht := tendsto_sourceStandardRootOmittedPartialProduct
    hp hp1 n ψ (x:ℂ)
  have hc := continuous_conj.continuousAt.tendsto.comp ht
  have heq (N : ℕ) :
      conj (sourceStandardRootOmittedPartialProduct hp hp1 n N ((x:ℂ),ψ)) =
        sourceStandardRootOmittedPartialProduct hp hp1 n N ((x:ℂ),ψ) :=
    Complex.conj_eq_iff_im.mpr
      (sourceStandardRootOmittedPartialProduct_im_eq_zero_on_realGap
        hp hp1 ψ hreal n N x hx)
  simp only [Function.comp_def] at hc
  simp_rw [heq] at hc
  exact Complex.conj_eq_iff_im.mp (tendsto_nhds_unique hc ht)

end NLS.ZakharovShabat
