import NLS.ZakharovShabat.SourcePsiVariationCutoffFormula

/-!
# Finite resolvent form of the psi variation

Off the retained roots, each differentiated factor of the finite
deleted product can be divided by its original factor. The product
rule then becomes the original product times a finite root-resolvent
sum, the finite version of the formula used in Lemma 12.7.
-/

noncomputable section
open Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The root-direction derivative of a finite single-root product is
the product times its finite logarithmic-derivative sum. -/
theorem deriv_finiteSingleSpectralProduct_rootLine_eq_mul_resolvent
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (s : Finset ℤ) (a h : Coeff p) (z : ℂ)
    (havoid : ∀ m ∈ s, z ≠ displacedRoots a m) :
    deriv (fun t : ℂ => ∏ m ∈ s,
      singleSpectralFactor (displacedRoots (a + t • h)) z m) 0 =
      (∏ m ∈ s, singleSpectralFactor (displacedRoots a) z m) *
        ∑ m ∈ s, h m / (displacedRoots a m - z) := by
  let F : ℤ → ℂ := fun m => singleSpectralFactor (displacedRoots a) z m
  have hfactor (m : ℤ) (hm : m ∈ s) :
      F m * (h m / (displacedRoots a m - z)) =
        h m / singleSpectralDenominator m := by
    have hroot : displacedRoots a m - z ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (havoid m hm))
    have hden := singleSpectralDenominator_ne_zero m
    dsimp [F,singleSpectralFactor]
    field_simp
  rw [deriv_finiteSingleSpectralProduct_rootLine]
  change (∑ m ∈ s, (∏ j ∈ s.erase m, F j) *
      (h m / singleSpectralDenominator m)) =
    (∏ m ∈ s, F m) *
      ∑ m ∈ s, h m / (displacedRoots a m - z)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [← hfactor m hm, ← Finset.mul_prod_erase s F hm]
  ring

/-- The literal deleted psi cutoff has the same finite resolvent
identity, including its exceptional index normalization. -/
theorem deriv_sourcePsiCandidate_cutoff_eq_mul_resolvent
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (n : ℤ) (N : ℕ) (a h : Coeff p) (z : ℂ)
    (havoid : ∀ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
      z ≠ displacedRoots a m) :
    deriv (fun t : ℂ => -2 *
      jointDeletedSingleSpectralPartialProduct n N (z,a + t • h)) 0 =
      (-2 * jointDeletedSingleSpectralPartialProduct n N (z,a)) *
        ∑ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
          h m / (displacedRoots a m - z) := by
  let s : Finset ℤ := (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n
  have heq : (fun t : ℂ => -2 *
      jointDeletedSingleSpectralPartialProduct n N (z,a + t • h)) =
      fun t : ℂ => (-2 / singleSpectralDenominator n) *
        ∏ m ∈ s,
          singleSpectralFactor (displacedRoots (a + t • h)) z m := by
    funext t
    unfold jointDeletedSingleSpectralPartialProduct
    dsimp [s]
    ring
  rw [heq, deriv_const_mul_field,
    deriv_finiteSingleSpectralProduct_rootLine_eq_mul_resolvent s a h z havoid]
  unfold jointDeletedSingleSpectralPartialProduct
  dsimp [s]
  ring

/-- Away from every retained root, the products of the literal
cutoffs and finite root-resolvent sums converge to the entire
psi-numerator variation. -/
theorem tendsto_sourcePsiCandidateVariation_cutoff_mul_resolvent
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a h : Coeff p) (z : ℂ)
    (havoid : ∀ m : ℤ, m ≠ n → z ≠ displacedRoots a m) :
    Tendsto
      (fun N : ℕ =>
        (-2 * jointDeletedSingleSpectralPartialProduct n N (z,a)) *
          ∑ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
            h m / (displacedRoots a m - z))
      atTop (𝓝 (sourcePsiCandidateVariation n a h z)) := by
  have hcut (N : ℕ) : ∀ m ∈
      (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
      z ≠ displacedRoots a m := by
    intro m hm
    exact havoid m (Finset.mem_erase.mp hm).1
  have heq (N : ℕ) :=
    deriv_sourcePsiCandidate_cutoff_eq_mul_resolvent n N a h z (hcut N)
  simpa only [heq] using
    tendsto_deriv_sourcePsiCandidate_cutoff_rootLine hp hp1 n a h z

/-- Any identified limit of the finite root-resolvent sums gives the
corresponding exact formula for the entire numerator variation. -/
theorem sourcePsiCandidateVariation_eq_mul_resolventLimit
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a h : Coeff p) (z S : ℂ)
    (havoid : ∀ m : ℤ, m ≠ n → z ≠ displacedRoots a m)
    (hsum : Tendsto
      (fun N : ℕ =>
        ∑ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
          h m / (displacedRoots a m - z))
      atTop (𝓝 S)) :
    sourcePsiCandidateVariation n a h z =
      sourcePsiCandidate n (z,a) * S := by
  have hprod := tendsto_sourcePsiCandidate_partialProduct hp hp1 n (z,a)
  have hmul := hprod.mul hsum
  exact tendsto_nhds_unique
    (tendsto_sourcePsiCandidateVariation_cutoff_mul_resolvent
      hp hp1 n a h z havoid) hmul

end NLS.ZakharovShabat
