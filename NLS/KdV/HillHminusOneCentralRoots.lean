import NLS.KdV.HillHminusOneCentralCounting
import NLS.SequenceSpaces.OrderedFiniteEnumeration
import Mathlib.Data.Multiset.Filter

/-! # Actual ordered central H^-1 Hill roots

Construct the finite root multiset of the physical energy characteristic,
retain every analytic multiplicity, and enumerate its real values in
order. No caller supplies a root list or its cardinality.
-/

noncomputable section
set_option autoImplicit false
open Set Metric
open scoped Classical
namespace NLS.KdV

theorem hillHminusCentralRootSupport
    (q : PeriodOneHminusOne)
    (N : ℕ) (h : HillHminusCentralControl q N) :
    (fun z : ℂ => if z ∈ hillCentralDisc N then
      analyticOrderNatAt (hillHminusRadicand q) z else 0).HasFiniteSupport := by
  have hb : (hillCentralSeparator N : ℂ) ∈ hillCentralDisc N :=
    (ofReal_mem_hillCentralDisc_iff N _).mpr ⟨by
      linarith [hillCentralSeparator_pos N h.index_ge_two, sq_nonneg (N : ℝ)],le_rfl⟩
  exact ComplexAnalysis.analyticZeroCount_hasFiniteSupport (isCompact_closedBall _ _)
    (isConnected_closedBall (hillCentralRadius_pos N h.index_ge_two).le)
    ((analyticOnNhd_hillHminusRadicand _).mono (subset_univ _)) hb
    (h.separator_ne_zero _ rfl)

def hillHminusCentralRoots
    (q : PeriodOneHminusOne)
    (N : ℕ) (h : HillHminusCentralControl q N) : Multiset ℂ :=
  ComplexAnalysis.analyticZeroMultiset (hillHminusRadicand q)
    (hillCentralDisc N) (hillHminusCentralRootSupport q N h)

def hillHminusRealCentralRoots
    (q : PeriodOneHminusOne)
    (N : ℕ) (h : HillHminusCentralControl q N) : Multiset ℝ :=
  (hillHminusCentralRoots q N h).map Complex.re

theorem count_hillHminusCentralRoots
    (q : PeriodOneHminusOne)
    (N : ℕ) (h : HillHminusCentralControl q N) (z : ℂ) :
    (hillHminusCentralRoots q N h).count z =
      if z ∈ hillCentralDisc N then analyticOrderNatAt (hillHminusRadicand q) z
      else 0 := ComplexAnalysis.count_analyticZeroMultiset _ _ _ z

theorem mem_hillHminusCentralRoots_imp
    (q : PeriodOneHminusOne)
    (N : ℕ) (h : HillHminusCentralControl q N)
    {z : ℂ} (hz : z ∈ hillHminusCentralRoots q N h) :
    z ∈ hillCentralDisc N ∧ hillHminusRadicand q z = 0 :=
  ComplexAnalysis.mem_analyticZeroMultiset_imp _ _ _ hz

theorem card_hillHminusRealCentralRoots
    (q : PeriodOneHminusOne)
    (hreal : IsRealPeriodOneHminusOne q)
    (N : ℕ) (h : HillHminusCentralControl q N) :
    (hillHminusRealCentralRoots q N h).card = 2*N-1 := by
  rw [hillHminusRealCentralRoots, Multiset.card_map, hillHminusCentralRoots,
    ComplexAnalysis.card_analyticZeroMultiset, h.central_count hreal]

/-- Taking real parts loses no root or multiplicity on a real potential. -/
theorem map_ofReal_hillHminusRealCentralRoots
    (q : PeriodOneHminusOne)
    (hreal : IsRealPeriodOneHminusOne q)
    (N : ℕ) (h : HillHminusCentralControl q N) :
    (hillHminusRealCentralRoots q N h).map Complex.ofReal = hillHminusCentralRoots q N h := by
  rw [hillHminusRealCentralRoots, Multiset.map_map]
  calc
    _ = (hillHminusCentralRoots q N h).map id := by
      apply Multiset.map_congr rfl
      intro z hz
      have hi := hillHminusRadicand_root_im_zero q hreal z
        (mem_hillHminusCentralRoots_imp q N h hz).2
      apply Complex.ext <;> simp [hi]
    _ = _ := Multiset.map_id _

theorem count_hillHminusRealCentralRoots
    (q : PeriodOneHminusOne)
    (hreal : IsRealPeriodOneHminusOne q)
    (N : ℕ) (h : HillHminusCentralControl q N) (x : ℝ) :
    (hillHminusRealCentralRoots q N h).count x =
      if (x : ℂ) ∈ hillCentralDisc N then
        analyticOrderNatAt (hillHminusRadicand q) x else 0 := by
  rw [← count_hillHminusCentralRoots q N h x,
    ← map_ofReal_hillHminusRealCentralRoots q hreal N h]
  exact (Multiset.count_map_eq_count' Complex.ofReal _ Complex.ofReal_injective x).symm

theorem mem_hillHminusRealCentralRoots_iff
    (q : PeriodOneHminusOne)
    (hreal : IsRealPeriodOneHminusOne q)
    (N : ℕ) (h : HillHminusCentralControl q N) (x : ℝ) :
    x ∈ hillHminusRealCentralRoots q N h ↔
      x ∈ Ioo (-(N : ℝ)^2) (hillCentralSeparator N) ∧
        hillHminusRadicand q x = 0 := by
  constructor
  · intro hx
    obtain ⟨z,hz,hzx⟩ := Multiset.mem_map.mp hx
    have hzc := mem_hillHminusCentralRoots_imp q N h hz
    have hi := hillHminusRadicand_root_im_zero q hreal z hzc.2
    have he : (x : ℂ) = z := by apply Complex.ext <;> simp [← hzx,hi]
    have hx0 : hillHminusRadicand q x = 0 := he.symm ▸ hzc.2
    have hxd : (x : ℂ) ∈ hillCentralDisc N := he.symm ▸ hzc.1
    have hlo := h.root_lower x hx0
    have hhi := ((ofReal_mem_hillCentralDisc_iff N x).mp hxd).2
    have hne : x ≠ hillCentralSeparator N := by
      intro hxB
      exact h.separator_ne_zero x hxB hx0
    exact ⟨⟨hlo,lt_of_le_of_ne hhi hne⟩,hx0⟩
  · rintro ⟨hx,hx0⟩
    have hxd := (ofReal_mem_hillCentralDisc_iff N x).mpr ⟨hx.1.le,hx.2.le⟩
    have hb0 := h.separator_ne_zero
      (hillCentralSeparator N) rfl
    have hfinite := ComplexAnalysis.analyticOrderAt_ne_top_on_connected isPreconnected_univ
      (analyticOnNhd_hillHminusRadicand q) (mem_univ _) hb0 (mem_univ (x : ℂ))
    have hp := ComplexAnalysis.analyticOrderNatAt_pos_of_zero
      (analyticOnNhd_hillHminusRadicand _ x (mem_univ _)) hfinite hx0
    apply Multiset.count_pos.mp
    rwa [count_hillHminusRealCentralRoots q hreal N h x, if_pos hxd]

/-- Actual central roots admit a nondecreasing enumeration with exactly
their analytic multiplicities. The index set has 2*N-1 slots. -/
theorem exists_ordered_hillHminusCentralRoots
    (q : PeriodOneHminusOne)
    (hreal : IsRealPeriodOneHminusOne q)
    (N : ℕ) (h : HillHminusCentralControl q N) :
    ∃ xi : ℕ → ℝ,
      (∑ j ∈ Finset.range (2*N-1), ({xi j} : Multiset ℝ)) = hillHminusRealCentralRoots q N h ∧
      (∀ i < 2*N-1, ∀ j < 2*N-1, i ≤ j → xi i ≤ xi j) ∧
      ∀ x : ℝ, (∑ j ∈ Finset.range (2*N-1), if xi j = x then 1 else 0) =
        if (x : ℂ) ∈ hillCentralDisc N then
          analyticOrderNatAt (hillHminusRadicand q) x else 0 := by
  obtain ⟨xi,he,ho⟩ := NLS.exists_ordered_finset_multiset_enumeration (· ≤ ·)
    (Finset.range (2*N-1)) (hillHminusRealCentralRoots q N h)
    (by simpa only [Finset.card_range] using card_hillHminusRealCentralRoots q hreal N h)
  refine ⟨xi,he,?_,?_⟩
  · intro i hi j hj hij
    exact ho i (Finset.mem_range.mpr hi) j (Finset.mem_range.mpr hj) hij
  · intro x
    have hc := congrArg (fun s : Multiset ℝ => s.count x) he
    rw [count_hillHminusRealCentralRoots q hreal N h x] at hc
    simpa only [Multiset.count_sum', Multiset.count_singleton, eq_comm] using hc

end NLS.KdV
