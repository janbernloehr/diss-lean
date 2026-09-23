import NLS.ZakharovShabat.SourceStandardRootSqrtRemainder
import NLS.SequenceSpaces.Reflection
import NLS.SequenceSpaces.ExponentEmbedding
import NLS.SequenceSpaces.ProductRowExponents
import NLS.ZakharovShabat.SourceStandardRootContourBasic
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Convergence of the paired standard-root product

For Lemma 10.5 with the omitted index `0`, the normalized single-factor
error is an `ℓ²` sequence: midpoint and square-root corrections lie in
`ℓ¹`, while the free spectral term is a punctured reciprocal lattice.
Hölder makes the quadratic product of the `k` and `-k` errors `ℓ¹`.
The paired factors therefore have an absolutely summable deviation
from one and define a convergent infinite product.
-/

noncomputable section
open Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
private instance : (2 : ℝ≥0∞).HolderTriple 2 1 := by
  simpa using NLS.holderTriple_double 1

/-- The already summable source square-root corrections as an `ℓ¹`
coefficient sequence. -/
def sourceStandardRootSqrtCorrectionCoeff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (z : ℂ) : Coeff 1 :=
  ⟨sourceStandardRootSqrtCorrection hp hp1 ψ z,
    (memℓp_gen_iff (by norm_num : 0 < (1 : ℝ≥0∞).toReal)).mpr (by
      simpa only [ENNReal.toReal_one, Real.rpow_one] using
        summable_norm_sourceStandardRootSqrtCorrection hp hp1 ψ z)⟩

@[simp] theorem sourceStandardRootSqrtCorrectionCoeff_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) (k : ℤ) :
    sourceStandardRootSqrtCorrectionCoeff hp hp1 ψ z k =
      sourceStandardRootSqrtCorrection hp hp1 ψ z k := rfl

/-- The complete normalized single-factor error, with its undefined
central normalization replaced by zero, belongs to `ℓ²`. -/
def sourceStandardRootRelativeErrorCoeff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (z : ℂ) : Coeff 2 :=
  Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (sourceStandardRootMidpointCorrection hp hp1 ψ) +
    Coeff.exponentInclusion (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (sourceStandardRootSqrtCorrectionCoeff hp hp1 ψ z) -
    (z / (Real.pi : ℂ)) • Coeff.puncturedLattice 2 (by norm_num)

@[simp] theorem sourceStandardRootRelativeErrorCoeff_apply_of_ne
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ)
    (k : ℤ) (hk : k ≠ 0) :
    sourceStandardRootRelativeErrorCoeff hp hp1 ψ z k =
      sourceStandardRootRelativeError hp hp1 ψ k z := by
  simp only [sourceStandardRootRelativeErrorCoeff, lp.coeFn_sub, Pi.sub_apply,
    lp.coeFn_add, Pi.add_apply, Coeff.exponentInclusion_apply,
    sourceStandardRootMidpointCorrection_apply, if_neg hk,
    sourceStandardRootSqrtCorrectionCoeff_apply,
    sourceStandardRootSqrtCorrection, Coeff.puncturedLattice_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [sourceStandardRootRelativeError_eq hp hp1 ψ k z hk]
  unfold standardRootSqrtCorrection
  field_simp
  ring

@[simp] theorem sourceStandardRootRelativeErrorCoeff_apply_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) :
    sourceStandardRootRelativeErrorCoeff hp hp1 ψ z 0 = 0 := by
  simp only [sourceStandardRootRelativeErrorCoeff, lp.coeFn_sub, Pi.sub_apply,
    lp.coeFn_add, Pi.add_apply, Coeff.exponentInclusion_apply,
    sourceStandardRootMidpointCorrection_apply,
    sourceStandardRootSqrtCorrectionCoeff_apply,
    sourceStandardRootSqrtCorrection, Coeff.puncturedLattice_apply,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  simp

/-- The `ℓ¹` coefficient sequence of paired-factor deviations from one. -/
def sourceStandardRootPairExcessCoeff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (z : ℂ) : Coeff 1 :=
  let b := sourceStandardRootMidpointCorrection hp hp1 ψ
  let r := sourceStandardRootSqrtCorrectionCoeff hp hp1 ψ z
  let a := sourceStandardRootRelativeErrorCoeff hp hp1 ψ z
  b + Coeff.reflection b + r + Coeff.reflection r +
    Coeff.holderProduct (q := 1) a (Coeff.reflection a)

/-- At each noncentral index this `ℓ¹` coefficient is exactly the
paired-factor deviation `a_k+a_{-k}+a_ka_{-k}`. -/
theorem sourceStandardRootPairExcessCoeff_apply_of_ne
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ)
    (k : ℤ) (hk : k ≠ 0) :
    sourceStandardRootPairExcessCoeff hp hp1 ψ z k =
      sourceStandardRootRelativeError hp hp1 ψ k z +
      sourceStandardRootRelativeError hp hp1 ψ (-k) z +
      sourceStandardRootRelativeError hp hp1 ψ k z *
        sourceStandardRootRelativeError hp hp1 ψ (-k) z := by
  simp only [sourceStandardRootPairExcessCoeff, lp.coeFn_add, Pi.add_apply,
    Coeff.reflection_apply, Coeff.holderProduct_apply,
    sourceStandardRootRelativeErrorCoeff_apply_of_ne hp hp1 ψ z k hk,
    sourceStandardRootRelativeErrorCoeff_apply_of_ne hp hp1 ψ z (-k)
      (neg_ne_zero.mpr hk), sourceStandardRootSqrtCorrectionCoeff_apply]
  rw [sourceStandardRootRelativeError_pair hp hp1 ψ k z hk]
  simp only [sourceStandardRootMidpointCorrection_apply, if_neg hk,
    if_neg (neg_ne_zero.mpr hk), sourceStandardRootSqrtCorrection]
  unfold standardRootSqrtCorrection
  simp only [Int.cast_neg, mul_neg]

/-- The paired excess is absolutely summable. Hölder has already
placed its quadratic cross term in `ℓ¹`. -/
theorem summable_norm_sourceStandardRootPairExcessCoeff
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) :
    Summable (fun k : ℤ => ‖sourceStandardRootPairExcessCoeff hp hp1 ψ z k‖) := by
  simpa only [ENNReal.toReal_one, Real.rpow_one] using
    (lp.memℓp (sourceStandardRootPairExcessCoeff hp hp1 ψ z)).summable
      (by norm_num : 0 < (1 : ℝ≥0∞).toReal)

/-- The nonzero-index pair numbered by `j` consists of roots at
the indices `j+1` and `-(j+1)`. -/
def sourceStandardRootPairedFactor (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (z : ℂ) (j : ℕ) : ℂ :=
  let k : ℤ := (j+1 : ℕ)
  (sourceStandardRoot hp hp1 ψ k z / ((Real.pi : ℂ)*k)) *
    (sourceStandardRoot hp hp1 ψ (-k) z / (-((Real.pi : ℂ)*k)))

/-- Every paired factor is one plus its `ℓ¹` excess coefficient. -/
theorem sourceStandardRootPairedFactor_eq_one_add
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) (j : ℕ) :
    sourceStandardRootPairedFactor hp hp1 ψ z j =
      1 + sourceStandardRootPairExcessCoeff hp hp1 ψ z ((j+1 : ℕ) : ℤ) := by
  let k : ℤ := (j+1 : ℕ)
  have hk : k ≠ 0 := by dsimp [k]; omega
  rw [sourceStandardRootPairExcessCoeff_apply_of_ne hp hp1 ψ z k hk]
  change (sourceStandardRoot hp hp1 ψ k z / ((Real.pi : ℂ)*k)) *
    (sourceStandardRoot hp hp1 ψ (-k) z / (-((Real.pi : ℂ)*k))) = _
  rw [sourceStandardRoot_pair_factor]
  ring

/-- Absolute summability of the paired deviations on the positive
index set. -/
theorem summable_norm_sourceStandardRootPairedFactor_sub_one
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) :
    Summable (fun j : ℕ => ‖sourceStandardRootPairedFactor hp hp1 ψ z j - 1‖) := by
  have hs := summable_norm_sourceStandardRootPairExcessCoeff hp hp1 ψ z
  have hinj : Function.Injective (fun j : ℕ => ((j+1 : ℕ) : ℤ)) := by
    intro a b h
    have hnat : a+1 = b+1 := Int.ofNat_injective h
    omega
  have h := hs.comp_injective hinj
  simpa only [sourceStandardRootPairedFactor_eq_one_add, add_sub_cancel_left,
    Function.comp_def] using h

/-- The infinite standard-root product with the central index omitted. -/
def sourceStandardRootPairedProduct (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  ∏' j : ℕ, sourceStandardRootPairedFactor hp hp1 ψ z j

/-- The product converges at every source potential and complex spectral
parameter, including points where an individual factor vanishes. -/
theorem multipliable_sourceStandardRootPairedFactor
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) :
    Multipliable (sourceStandardRootPairedFactor hp hp1 ψ z) := by
  rw [show sourceStandardRootPairedFactor hp hp1 ψ z =
      fun j => 1 + sourceStandardRootPairExcessCoeff hp hp1 ψ z ((j+1 : ℕ) : ℤ)
    from funext (sourceStandardRootPairedFactor_eq_one_add hp hp1 ψ z)]
  apply multipliable_one_add_of_summable
  have hs := summable_norm_sourceStandardRootPairExcessCoeff hp hp1 ψ z
  have hinj : Function.Injective (fun j : ℕ => ((j+1 : ℕ) : ℤ)) := by
    intro a b h
    have hnat : a+1 = b+1 := Int.ofNat_injective h
    omega
  simpa only [Function.comp_def] using hs.comp_injective hinj

/-- Finite paired products converge to the standard-root product. -/
theorem tendsto_sourceStandardRootPairedProduct
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ) :
    Tendsto (fun N : ℕ => ∏ j ∈ Finset.range N,
      sourceStandardRootPairedFactor hp hp1 ψ z j) atTop
      (𝓝 (sourceStandardRootPairedProduct hp hp1 ψ z)) :=
  (multipliable_sourceStandardRootPairedFactor hp hp1 ψ z).tendsto_prod_tprod_nat

/-- For the omitted central index, the domain of Lemma 10.5 is the
complement of every other canonical periodic gap segment. -/
def sourceStandardRootPairedDomain (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) : Set ℂ :=
  {z | ∀ k : ℤ, k ≠ 0 → z ∉ sourcePeriodicSegment hp hp1 ψ k}

/-- None of the paired factors vanishes off the noncentral gaps. -/
theorem sourceStandardRootPairedFactor_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceStandardRootPairedDomain hp hp1 ψ) (j : ℕ) :
    sourceStandardRootPairedFactor hp hp1 ψ z j ≠ 0 := by
  let k : ℤ := (j+1 : ℕ)
  have hk : k ≠ 0 := by dsimp [k]; omega
  have hπ : (Real.pi : ℂ)*k ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (by exact_mod_cast hk)
  have hpos := sourceStandardRoot_ne_zero_off_segment hp hp1 ψ k z (hz k hk)
  have hneg := sourceStandardRoot_ne_zero_off_segment hp hp1 ψ (-k) z
    (hz (-k) (neg_ne_zero.mpr hk))
  change (sourceStandardRoot hp hp1 ψ k z / ((Real.pi : ℂ)*k)) *
    (sourceStandardRoot hp hp1 ψ (-k) z / (-((Real.pi : ℂ)*k))) ≠ 0
  exact mul_ne_zero (div_ne_zero hpos hπ) (div_ne_zero hneg (neg_ne_zero.mpr hπ))

/-- The infinite paired product has no spurious zeros on the domain
of Lemma 10.5 for the omitted central index. -/
theorem sourceStandardRootPairedProduct_ne_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (z : ℂ)
    (hz : z ∈ sourceStandardRootPairedDomain hp hp1 ψ) :
    sourceStandardRootPairedProduct hp hp1 ψ z ≠ 0 := by
  rw [sourceStandardRootPairedProduct,
    show sourceStandardRootPairedFactor hp hp1 ψ z =
      fun j => 1 + sourceStandardRootPairExcessCoeff hp hp1 ψ z ((j+1 : ℕ) : ℤ)
    from funext (sourceStandardRootPairedFactor_eq_one_add hp hp1 ψ z)]
  apply tprod_one_add_ne_zero_of_summable
  · intro j
    rw [← sourceStandardRootPairedFactor_eq_one_add hp hp1 ψ z j]
    exact sourceStandardRootPairedFactor_ne_zero hp hp1 ψ z hz j
  · have hs := summable_norm_sourceStandardRootPairExcessCoeff hp hp1 ψ z
    have hinj : Function.Injective (fun j : ℕ => ((j+1 : ℕ) : ℤ)) := by
      intro a b h
      have hnat : a+1 = b+1 := Int.ofNat_injective h
      omega
    simpa only [Function.comp_def] using hs.comp_injective hinj

end NLS.ZakharovShabat
