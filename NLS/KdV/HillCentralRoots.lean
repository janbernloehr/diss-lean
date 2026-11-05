import NLS.KdV.HillCentralCounting
import NLS.SequenceSpaces.OrderedFiniteEnumeration
import Mathlib.Data.Multiset.Filter

/-! # Actual ordered central Hill roots

Construct the finite root multiset of the physical energy characteristic,
retain every analytic multiplicity, and enumerate its real values in
order. No caller supplies a root list or its cardinality.
-/

noncomputable section
open Set Metric
open scoped Classical
namespace NLS.KdV

theorem hillCentralRootSupport
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ)) :
    (fun z : ℂ => if z ∈ hillCentralDisc N then
      analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) z else 0).HasFiniteSupport := by
  have hb : (hillCentralSeparator N : ℂ) ∈ hillCentralDisc N :=
    (ofReal_mem_hillCentralDisc_iff N _).mpr ⟨by
      linarith [hillCentralSeparator_pos N hN, sq_nonneg (N : ℝ)],le_rfl⟩
  exact ComplexAnalysis.analyticZeroCount_hasFiniteSupport (isCompact_closedBall _ _)
    (isConnected_closedBall (hillCentralRadius_pos N hN).le)
    ((analyticOnNhd_hillL2Radicand _).mono (subset_univ _)) hb
    (hillL2Radicand_ne_zero_on_central_separator q hq N hN hcut _ rfl)

def hillCentralRoots
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ)) : Multiset ℂ :=
  ComplexAnalysis.analyticZeroMultiset (hillL2Radicand (SpectralWeight.one.toCoeff q))
    (hillCentralDisc N) (hillCentralRootSupport q hq N hN hcut)

def hillRealCentralRoots
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ)) : Multiset ℝ :=
  (hillCentralRoots q hq N hN hcut).map Complex.re

theorem count_hillCentralRoots
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ)) (z : ℂ) :
    (hillCentralRoots q hq N hN hcut).count z =
      if z ∈ hillCentralDisc N then analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) z
      else 0 := ComplexAnalysis.count_analyticZeroMultiset _ _ _ z

theorem mem_hillCentralRoots_imp
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ))
    {z : ℂ} (hz : z ∈ hillCentralRoots q hq N hN hcut) :
    z ∈ hillCentralDisc N ∧ hillL2Radicand (SpectralWeight.one.toCoeff q) z = 0 :=
  ComplexAnalysis.mem_analyticZeroMultiset_imp _ _ _ hz

theorem card_hillRealCentralRoots
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ)) :
    (hillRealCentralRoots q hq N hN hcut).card = 2*N-1 := by
  rw [hillRealCentralRoots, Multiset.card_map, hillCentralRoots,
    ComplexAnalysis.card_analyticZeroMultiset, hillL2Radicand_central_count q hq hreal N hN hcut]

/-- Taking real parts loses no root or multiplicity on a real potential. -/
theorem map_ofReal_hillRealCentralRoots
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ)) :
    (hillRealCentralRoots q hq N hN hcut).map Complex.ofReal = hillCentralRoots q hq N hN hcut := by
  rw [hillRealCentralRoots, Multiset.map_map]
  calc
    _ = (hillCentralRoots q hq N hN hcut).map id := by
      apply Multiset.map_congr rfl
      intro z hz
      have hi := hillL2Discriminant_root_im_zero q hq hreal z
        (sub_eq_zero.mp (mem_hillCentralRoots_imp q hq N hN hcut hz).2)
      apply Complex.ext <;> simp [hi]
    _ = _ := Multiset.map_id _

theorem count_hillRealCentralRoots
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ)) (x : ℝ) :
    (hillRealCentralRoots q hq N hN hcut).count x =
      if (x : ℂ) ∈ hillCentralDisc N then
        analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) x else 0 := by
  rw [← count_hillCentralRoots q hq N hN hcut x,
    ← map_ofReal_hillRealCentralRoots q hq hreal N hN hcut]
  exact (Multiset.count_map_eq_count' Complex.ofReal _ Complex.ofReal_injective x).symm

theorem mem_hillRealCentralRoots_iff
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ)) (x : ℝ) :
    x ∈ hillRealCentralRoots q hq N hN hcut ↔
      x ∈ Ioo (-(N : ℝ)^2) (hillCentralSeparator N) ∧
        hillL2Radicand (SpectralWeight.one.toCoeff q) x = 0 := by
  constructor
  · intro hx
    obtain ⟨z,hz,hzx⟩ := Multiset.mem_map.mp hx
    have hzc := mem_hillCentralRoots_imp q hq N hN hcut hz
    have hi := hillL2Discriminant_root_im_zero q hq hreal z (sub_eq_zero.mp hzc.2)
    have he : (x : ℂ) = z := by apply Complex.ext <;> simp [← hzx,hi]
    have hx0 : hillL2Radicand (SpectralWeight.one.toCoeff q) x = 0 := he.symm ▸ hzc.2
    have hxd : (x : ℂ) ∈ hillCentralDisc N := he.symm ▸ hzc.1
    have hlo := hillL2Radicand_re_lower_bound q hq N (by omega) hcut x hx0
    have hhi := ((ofReal_mem_hillCentralDisc_iff N x).mp hxd).2
    have hne : x ≠ hillCentralSeparator N := by
      intro hxB
      exact hillL2Radicand_ne_zero_on_central_separator q hq N hN hcut x hxB hx0
    exact ⟨⟨hlo,lt_of_le_of_ne hhi hne⟩,hx0⟩
  · rintro ⟨hx,hx0⟩
    have hxd := (ofReal_mem_hillCentralDisc_iff N x).mpr ⟨hx.1.le,hx.2.le⟩
    have hb0 := hillL2Radicand_ne_zero_on_central_separator q hq N hN hcut
      (hillCentralSeparator N) rfl
    have hfinite := ComplexAnalysis.analyticOrderAt_ne_top_on_connected isPreconnected_univ
      (analyticOnNhd_hillL2Radicand (SpectralWeight.one.toCoeff q)) (mem_univ _) hb0 (mem_univ (x : ℂ))
    have hp := ComplexAnalysis.analyticOrderNatAt_pos_of_zero
      (analyticOnNhd_hillL2Radicand _ x (mem_univ _)) hfinite hx0
    apply Multiset.count_pos.mp
    rwa [count_hillRealCentralRoots q hq hreal N hN hcut x, if_pos hxd]

/-- Actual central roots admit a nondecreasing enumeration with exactly
their analytic multiplicities. The index set has 2*N-1 slots. -/
theorem exists_ordered_hillCentralRoots
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ)) :
    ∃ xi : ℕ → ℝ,
      (∑ j ∈ Finset.range (2*N-1), ({xi j} : Multiset ℝ)) = hillRealCentralRoots q hq N hN hcut ∧
      (∀ i < 2*N-1, ∀ j < 2*N-1, i ≤ j → xi i ≤ xi j) ∧
      ∀ x : ℝ, (∑ j ∈ Finset.range (2*N-1), if xi j = x then 1 else 0) =
        if (x : ℂ) ∈ hillCentralDisc N then
          analyticOrderNatAt (hillL2Radicand (SpectralWeight.one.toCoeff q)) x else 0 := by
  obtain ⟨xi,he,ho⟩ := NLS.exists_ordered_finset_multiset_enumeration (· ≤ ·)
    (Finset.range (2*N-1)) (hillRealCentralRoots q hq N hN hcut)
    (by simpa only [Finset.card_range] using card_hillRealCentralRoots q hq hreal N hN hcut)
  refine ⟨xi,he,?_,?_⟩
  · intro i hi j hj hij
    exact ho i (Finset.mem_range.mpr hi) j (Finset.mem_range.mpr hj) hij
  · intro x
    have hc := congrArg (fun s : Multiset ℝ => s.count x) he
    rw [count_hillRealCentralRoots q hq hreal N hN hcut x] at hc
    simpa only [Multiset.count_sum', Multiset.count_singleton, eq_comm] using hc

end NLS.KdV
