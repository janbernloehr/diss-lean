import NLS.ZakharovShabat.CriticalPointProducts
import NLS.ComplexAnalysis.FiniteProductOrders

/-!
# Finite single-product orders

Each occurrence of a root contributes one to the analytic order. Complete
critical labelings have finite root fibers, so their cutoff multiplicities
stabilize to the discriminant derivative's analytic multiplicity.
-/

noncomputable section
open Filter Topology
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- Nonzero normalization leaves each single factor with its one-root order. -/
theorem analyticOrderAt_singleSpectralFactor (ξ : ℤ → ℂ) (z : ℂ) (n : ℤ) :
    analyticOrderAt (fun t => singleSpectralFactor ξ t n) z = if ξ n = z then 1 else 0 := by
  unfold singleSpectralFactor
  rw [NLS.ComplexAnalysis.analyticOrderAt_div_const _ _ _
    (singleSpectralDenominator_ne_zero n) (by fun_prop),
    NLS.ComplexAnalysis.analyticOrderAt_const_sub]

/-- The finite cutoff order counts every repeated root once per occurrence. -/
theorem analyticOrderAt_singleSpectralPartialProduct (ξ : ℤ → ℂ) (z : ℂ) (N : ℕ) :
    analyticOrderAt (fun t => singleSpectralPartialProduct ξ t N) z =
      ((∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), if ξ n = z then (1 : ℕ) else 0) : ℕ∞) := by
  have ha : AnalyticAt ℂ (fun t => ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      singleSpectralFactor ξ t n) z :=
    Finset.analyticAt_fun_prod _ (fun n _ =>
      (analyticAt_const.sub analyticAt_id).div analyticAt_const (singleSpectralDenominator_ne_zero n))
  change analyticOrderAt ((fun _ : ℂ => (2 : ℂ)) *
    (fun t => ∏ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), singleSpectralFactor ξ t n)) z = _
  rw [analyticOrderAt_mul analyticAt_const ha,
    show analyticOrderAt (fun _ : ℂ => (2 : ℂ)) z = 0 from
      analyticOrderAt_eq_zero.mpr (Or.inr (by norm_num)), zero_add]
  rw [NLS.ComplexAnalysis.analyticOrderAt_finsetProd _ (fun n t => singleSpectralFactor ξ t n) z (fun n _ =>
    (analyticAt_const.sub analyticAt_id).div analyticAt_const (singleSpectralDenominator_ne_zero n))]
  simp only [analyticOrderAt_singleSpectralFactor, Nat.cast_one]

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {φ : PairSpace p} {hφ : φ ∈ pairParitySubspace 0}
variable {N : ℕ} {ξ : ℤ → ℂ}

/-- A complete critical sequence has finitely many occurrences of each root. -/
theorem CriticalPointLabeling.finite_fiber (h : CriticalPointLabeling hp hp1 φ hφ N ξ) (z : ℂ) :
    {n | ξ n = z}.Finite := by
  by_cases hf : ∃ n, N < n.natAbs ∧ ξ n = z
  · obtain ⟨n, hn, hz⟩ := hf
    exact (Set.finite_singleton n).subset (fun m hm =>
      h.eq_index_of_distant n hn m (hm.trans hz.symm))
  · apply (Finset.finite_toSet (Finset.Icc (-(N : ℤ)) (N : ℤ))).subset
    intro n hn
    have hsmall : n.natAbs ≤ N := by
      by_contra hlarge
      exact hf ⟨n, by omega, hn⟩
    simp only [Finset.mem_coe, Finset.mem_Icc]
    omega

/-- Cutoff orders eventually equal the exact critical multiplicity, including repeated central roots. -/
theorem CriticalPointLabeling.eventually_cutoff_order (h : CriticalPointLabeling hp hp1 φ hφ N ξ)
    (z : ℂ) : ∀ᶠ M : ℕ in atTop,
      analyticOrderAt (fun t => singleSpectralPartialProduct ξ t M) z =
        (analyticOrderNatAt (deriv (canonicalDiscriminant hp φ)) z : ℕ∞) := by
  have hs := h.finite_fiber z
  filter_upwards [Finset.tendsto_Icc_neg.eventually (eventually_ge_atTop hs.toFinset)] with M hM
  have he : (∑ᶠ n : ℤ, if ξ n = z then (1 : ℕ) else 0) =
      ∑ n ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), if ξ n = z then (1 : ℕ) else 0 := by
    apply finsum_eq_sum_of_support_subset
    intro n hn
    have hz : ξ n = z := by
      simpa only [Function.mem_support, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] using hn
    exact hM (hs.mem_toFinset.mpr hz)
  rw [h.multiplicity z] at he
  rw [analyticOrderAt_singleSpectralPartialProduct]
  simpa only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using
    congrArg (fun n : ℕ => (n : ℕ∞)) he.symm

end NLS.ZakharovShabat
