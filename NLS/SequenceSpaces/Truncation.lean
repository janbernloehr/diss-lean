import NLS.SequenceSpaces.Basic

/-!
# Finite Fourier truncations

The projections below are indexed by arbitrary finite sets of frequencies. Their
convergence requires `p < ∞`; the projection identities and contraction estimates
also hold at `p = ∞`.
-/

open scoped BigOperators ENNReal
open Filter
noncomputable section

namespace NLS
namespace Coeff

variable {p : ℝ≥0∞}

/-- Retain exactly the Fourier coefficients in `s`. -/
def truncate (s : Finset ℤ) (a : Coeff p) : Coeff p :=
  ∑ n ∈ s, lp.single p n (a n)

@[simp]
theorem truncate_apply (s : Finset ℤ) (a : Coeff p) (n : ℤ) :
    truncate s a n = if n ∈ s then a n else 0 := by
  change (lp.evalₗ (𝕜 := ℂ) (fun _ : ℤ => ℂ) p n)
    (∑ i ∈ s, lp.single p i (a i)) = _
  rw [map_sum]
  simp [lp.evalₗ_apply, lp.single_apply, Pi.single_apply]

@[simp]
theorem truncate_empty (a : Coeff p) : truncate ∅ a = 0 := by
  simp [truncate]

@[simp]
theorem truncate_add (s : Finset ℤ) (a b : Coeff p) :
    truncate s (a + b) = truncate s a + truncate s b := by
  ext n
  by_cases hn : n ∈ s <;> simp [hn]

@[simp]
theorem truncate_smul (s : Finset ℤ) (c : ℂ) (a : Coeff p) :
    truncate s (c • a) = c • truncate s a := by
  ext n
  by_cases hn : n ∈ s <;> simp [hn]

@[simp]
theorem truncate_truncate (s t : Finset ℤ) (a : Coeff p) :
    truncate s (truncate t a) = truncate (s ∩ t) a := by
  ext n
  by_cases hs : n ∈ s <;> by_cases ht : n ∈ t <;> simp [hs, ht]

@[simp]
theorem truncate_idempotent (s : Finset ℤ) (a : Coeff p) :
    truncate s (truncate s a) = truncate s a := by
  simp

/-- Truncating frequencies does not increase the sequence norm. -/
theorem norm_truncate_le (hp : p ≠ 0) (s : Finset ℤ) (a : Coeff p) :
    ‖truncate s a‖ ≤ ‖a‖ := by
  apply lp.norm_mono hp
  intro n
  by_cases hn : n ∈ s <;> simp [hn]

/-- Removing finitely many frequencies does not increase the sequence norm. -/
theorem norm_sub_truncate_le (hp : p ≠ 0) (s : Finset ℤ) (a : Coeff p) :
    ‖a - truncate s a‖ ≤ ‖a‖ := by
  apply lp.norm_mono hp
  intro n
  by_cases hn : n ∈ s <;> simp [hn]

/-- The finite Fourier projection as a linear map. -/
def truncateLinear (s : Finset ℤ) : Coeff p →ₗ[ℂ] Coeff p where
  toFun := truncate s
  map_add' := truncate_add s
  map_smul' := truncate_smul s

/-- The finite Fourier projection as a continuous linear map. -/
def truncateCLM [Fact (1 ≤ p)] (s : Finset ℤ) : Coeff p →L[ℂ] Coeff p :=
  (truncateLinear s).mkContinuous 1 (by
    intro a
    simpa only [one_mul, truncateLinear, LinearMap.coe_mk, AddHom.coe_mk] using
      norm_truncate_le (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)) s a)

@[simp]
theorem truncateCLM_apply [Fact (1 ≤ p)] (s : Finset ℤ) (a : Coeff p) :
    truncateCLM s a = truncate s a := rfl

/-- Finite Fourier truncations converge in norm for finite Banach exponents. -/
theorem tendsto_truncate [Fact (1 ≤ p)] (hp : p ≠ ⊤) (a : Coeff p) :
    Tendsto (fun s : Finset ℤ => truncate s a) atTop (nhds a) :=
  lp.hasSum_single hp a

/-- An explicit finite-support predicate useful before distribution realization. -/
def HasFiniteSupport (a : Coeff p) : Prop :=
  ∃ s : Finset ℤ, ∀ n ∉ s, a n = 0

theorem truncate_hasFiniteSupport (s : Finset ℤ) (a : Coeff p) :
    HasFiniteSupport (truncate s a) := by
  exact ⟨s, fun n hn => by simp [hn]⟩

/-- Finitely supported coefficients are dense in every finite Banach `lp` space. -/
theorem dense_finiteSupport [Fact (1 ≤ p)] (hp : p ≠ ⊤) :
    Dense {a : Coeff p | HasFiniteSupport a} := by
  intro a
  exact mem_closure_of_tendsto (tendsto_truncate hp a)
    (Eventually.of_forall fun s => truncate_hasFiniteSupport s a)

end Coeff
end NLS
