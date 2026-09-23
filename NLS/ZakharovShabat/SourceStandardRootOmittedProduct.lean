import NLS.ZakharovShabat.SourceStandardRootOmittedFinite

/-!
# Pointwise convergence of standard-root products with arbitrary omission

Symmetric finite cutoffs split into the zero mode and paired positive/negative
modes. Deleting one root replaces one member of one pair by `1`; the other
paired factors are unchanged. Multipliability of the previously established
paired product therefore gives convergence of the literal cutoffs.
-/

noncomputable section
open Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A pair of symmetric factors with one prescribed integer index omitted. -/
def omittedSymmetricPairFactor (f : ℤ → ℂ) (n : ℤ) (j : ℕ) : ℂ :=
  let k : ℤ := (j : ℤ)+1
  (if k = n then 1 else f k) * (if -k = n then 1 else f (-k))

/-- A symmetric finite product with one index erased is the zero-mode
factor times the product of pairs with that index replaced by `1`. -/
theorem prod_Icc_erase_eq_omittedSymmetricPairs (f : ℤ → ℂ) (n : ℤ) (N : ℕ) :
    (∏ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n, f m) =
      (if n = 0 then 1 else f 0) *
        ∏ j ∈ Finset.range N, omittedSymmetricPairFactor f n j := by
  let g (m : ℤ) := if m = n then (1 : ℂ) else f m
  have hprod : (∏ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n, f m) =
      ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), g m := by
    calc
      _ = ∏ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n, g m :=
        Finset.prod_congr rfl (by
          intro m hm
          simp [g, (Finset.mem_erase.mp hm).1])
      _ = ∏ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), g m :=
        Finset.prod_erase _ (by simp [g])
  rw [hprod, prod_symmetric_interval]
  simp only [g, eq_comm (a := (0 : ℤ)) (b := n)]
  rfl

/-- The paired root factor used when one integer index is omitted. -/
def sourceStandardRootOmittedPairedFactor (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (z : ℂ) (n : ℤ) (j : ℕ) : ℂ :=
  omittedSymmetricPairFactor
    (fun m => sourceStandardRoot hp hp1 ψ m z / singleSpectralDenominator m) n j

/-- Outside the one pair containing `n`, the omitted pair is the original pair. -/
theorem sourceStandardRootOmittedPairedFactor_eq_of_ne
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) (n : ℤ)
    (j : ℕ) (hj : n.natAbs ≠ j+1) :
    sourceStandardRootOmittedPairedFactor hp hp1 ψ z n j =
      sourceStandardRootPairedFactor hp hp1 ψ z j := by
  have hpos : (j : ℤ)+1 ≠ n := by omega
  have hneg : -((j : ℤ)+1) ≠ n := by omega
  have hkpos : (j : ℤ)+1 ≠ 0 := by omega
  have hkneg : -((j : ℤ)+1) ≠ 0 := by omega
  unfold sourceStandardRootOmittedPairedFactor omittedSymmetricPairFactor
  dsimp only
  rw [if_neg hpos, if_neg hneg]
  unfold sourceStandardRootPairedFactor
  simp only [singleSpectralDenominator, if_neg hkpos, if_neg hkneg]
  congr 1
  have hk : (j : ℤ)+1 = ((j+1 : ℕ) : ℤ) := by omega
  rw [hk]
  simp only [Int.cast_neg, mul_neg]

/-- Removing one member of one paired block preserves absolute summability
of the deviations from `1`. -/
theorem summable_norm_sourceStandardRootOmittedPairedFactor_sub_one
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) (n : ℤ) :
    Summable (fun j => ‖sourceStandardRootOmittedPairedFactor hp hp1 ψ z n j - 1‖) := by
  have heq : (fun j => ‖sourceStandardRootPairedFactor hp hp1 ψ z j - 1‖) =ᶠ[cofinite]
      (fun j => ‖sourceStandardRootOmittedPairedFactor hp hp1 ψ z n j - 1‖) := by
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop n.natAbs] with j hj
    rw [sourceStandardRootOmittedPairedFactor_eq_of_ne hp hp1 ψ z n j (by omega)]
  exact (summable_norm_sourceStandardRootPairedFactor_sub_one hp hp1 ψ z).congr_cofinite heq

/-- Removing one member of one paired block preserves multipliability. -/
theorem multipliable_sourceStandardRootOmittedPairedFactor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) (n : ℤ) :
    Multipliable (sourceStandardRootOmittedPairedFactor hp hp1 ψ z n) := by
  convert multipliable_one_add_of_summable
    (summable_norm_sourceStandardRootOmittedPairedFactor_sub_one hp hp1 ψ z n) using 1
  funext j
  ring

/-- Every omitted paired factor is nonzero away from all unomitted gaps. -/
theorem sourceStandardRootOmittedPairedFactor_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) (n : ℤ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) (j : ℕ) :
    sourceStandardRootOmittedPairedFactor hp hp1 ψ z n j ≠ 0 := by
  have hsingle (m : ℤ) (hm : m ≠ n) :
      sourceStandardRoot hp hp1 ψ m z / singleSpectralDenominator m ≠ 0 :=
    div_ne_zero (sourceStandardRoot_ne_zero_off_segment hp hp1 ψ m z (hz m hm))
      (singleSpectralDenominator_ne_zero m)
  unfold sourceStandardRootOmittedPairedFactor omittedSymmetricPairFactor
  dsimp only
  apply mul_ne_zero
  · split_ifs with h
    · exact one_ne_zero
    · exact hsingle _ h
  · split_ifs with h
    · exact one_ne_zero
    · exact hsingle _ h

/-- The infinite product with arbitrary index `n` omitted, normalized
exactly as in Lemma 10.5. -/
def sourceStandardRootOmittedProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  ((if n = 0 then 1 else sourceStandardRoot hp hp1 ψ 0 z) /
    singleSpectralDenominator n) *
    ∏' j : ℕ, sourceStandardRootOmittedPairedFactor hp hp1 ψ z n j

/-- The arbitrary-index infinite product specializes to the established
omitted-zero paired product. -/
theorem sourceStandardRootOmittedProduct_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) :
    sourceStandardRootOmittedProduct hp hp1 0 ψ z =
      sourceStandardRootPairedProduct hp hp1 ψ z := by
  unfold sourceStandardRootOmittedProduct sourceStandardRootPairedProduct
  simp only [singleSpectralDenominator]
  simp only [ite_true, div_one, one_mul]
  apply tprod_congr
  intro j
  exact sourceStandardRootOmittedPairedFactor_eq_of_ne hp hp1 ψ z 0 j (by omega)

/-- The arbitrary-index product is nonzero wherever every unomitted
standard root avoids its gap segment. -/
theorem sourceStandardRootOmittedProduct_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) (n : ℤ)
    (hz : z ∈ sourceStandardRootOmittedDomain hp hp1 ψ n) :
    sourceStandardRootOmittedProduct hp hp1 n ψ z ≠ 0 := by
  unfold sourceStandardRootOmittedProduct
  apply mul_ne_zero
  · apply div_ne_zero _ (singleSpectralDenominator_ne_zero n)
    by_cases hn : n = 0
    · simp [hn]
    · simpa only [if_neg hn] using
        sourceStandardRoot_ne_zero_off_segment hp hp1 ψ 0 z (hz 0 (Ne.symm hn))
  · rw [show (fun j : ℕ => sourceStandardRootOmittedPairedFactor hp hp1 ψ z n j) =
        (fun j => 1 + (sourceStandardRootOmittedPairedFactor hp hp1 ψ z n j - 1))
        from funext (fun j => by ring)]
    apply tprod_one_add_ne_zero_of_summable
    · intro j
      have he : 1 + (sourceStandardRootOmittedPairedFactor hp hp1 ψ z n j - 1) =
          sourceStandardRootOmittedPairedFactor hp hp1 ψ z n j := by ring
      rw [he]
      exact sourceStandardRootOmittedPairedFactor_ne_zero hp hp1 ψ z n hz j
    · exact summable_norm_sourceStandardRootOmittedPairedFactor_sub_one hp hp1 ψ z n

/-- Every literal symmetric cutoff is the zero-mode prefactor times
the finite product of omitted paired factors. -/
theorem sourceStandardRootOmittedPartialProduct_eq_paired
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (N : ℕ)
    (ψ : CoeffPair p) (z : ℂ) :
    sourceStandardRootOmittedPartialProduct hp hp1 n N (z,ψ) =
      ((if n = 0 then 1 else sourceStandardRoot hp hp1 ψ 0 z) /
        singleSpectralDenominator n) *
        ∏ j ∈ Finset.range N,
          sourceStandardRootOmittedPairedFactor hp hp1 ψ z n j := by
  unfold sourceStandardRootOmittedPartialProduct
  rw [prod_Icc_erase_eq_omittedSymmetricPairs]
  simp only [sourceStandardRootOmittedPairedFactor]
  have hzero : singleSpectralDenominator 0 = 1 := by simp [singleSpectralDenominator]
  rw [hzero]
  ring

/-- The literal cutoffs converge to the arbitrary-index infinite product
at every source potential and spectral parameter. -/
theorem tendsto_sourceStandardRootOmittedPartialProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) (z : ℂ) :
    Tendsto (fun N : ℕ => sourceStandardRootOmittedPartialProduct hp hp1 n N (z,ψ))
      atTop (𝓝 (sourceStandardRootOmittedProduct hp hp1 n ψ z)) := by
  have hprod := (multipliable_sourceStandardRootOmittedPairedFactor hp hp1 ψ z n).tendsto_prod_tprod_nat
  have hconst : Tendsto (fun _ : ℕ =>
      (if n = 0 then 1 else sourceStandardRoot hp hp1 ψ 0 z) /
        singleSpectralDenominator n) atTop
      (𝓝 ((if n = 0 then 1 else sourceStandardRoot hp hp1 ψ 0 z) /
        singleSpectralDenominator n)) := tendsto_const_nhds
  have hmul := hconst.mul hprod
  simpa only [sourceStandardRootOmittedProduct,
    sourceStandardRootOmittedPartialProduct_eq_paired] using hmul

end NLS.ZakharovShabat
