import NLS.ZakharovShabat.PeriodicEndpointRootCounts

/-!
# Ordered slots for periodic endpoint pairs

A signed index and a two-valued slot form one lexicographically ordered
index. Finite slot counts retain both occurrences of a collapsed gap.
-/

noncomputable section
open Set Complex Metric
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat

/-- Select one of the two endpoint coordinates using a lexicographic slot index. -/
def periodicEndpointSlot (ξ η : ℤ → ℂ) (k : ℤ ×ₗ Fin 2) : ℂ :=
  if (ofLex k).2 = 0 then ξ (ofLex k).1 else η (ofLex k).1

/-- All endpoint slots in a finite central block. -/
def centralPeriodicSlots (N : ℕ) : Finset (ℤ ×ₗ Fin 2) :=
  ((Finset.Icc (-(N : ℤ)) N) ×ˢ Finset.univ).map toLex.toEmbedding

@[simp] theorem periodicEndpointSlot_left (ξ η : ℤ → ℂ) (n : ℤ) :
    periodicEndpointSlot ξ η (toLex (n,0)) = ξ n := by simp [periodicEndpointSlot]

@[simp] theorem periodicEndpointSlot_right (ξ η : ℤ → ℂ) (n : ℤ) :
    periodicEndpointSlot ξ η (toLex (n,1)) = η n := by simp [periodicEndpointSlot]

/-- Membership of the central slot set is exactly the signed index bound. -/
@[simp] theorem mem_centralPeriodicSlots (N : ℕ) (k : ℤ ×ₗ Fin 2) :
    k ∈ centralPeriodicSlots N ↔ (ofLex k).1.natAbs ≤ N := by
  simp only [centralPeriodicSlots, Finset.mem_map, Finset.mem_product, Finset.mem_univ, and_true,
    Function.Embedding.coeFn_mk, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨n,a⟩,hn,rfl⟩
    change n.natAbs ≤ N
    omega
  · intro hn
    exact ⟨ofLex k,by change -(N : ℤ) ≤ (ofLex k).1 ∧ (ofLex k).1 ≤ N; omega,rfl⟩

/-- Each slot is one of the two endpoints at its signed index. -/
theorem periodicEndpointSlot_mem_pair (ξ η : ℤ → ℂ) (k : ℤ ×ₗ Fin 2) :
    ξ (ofLex k).1 = periodicEndpointSlot ξ η k ∨ η (ofLex k).1 = periodicEndpointSlot ξ η k := by
  unfold periodicEndpointSlot
  split_ifs <;> simp

/-- Global paired ordering gives global ordering on all slot indices. -/
theorem periodicEndpointSlot_ordered (ξ η : ℤ → ℂ)
    (hw : ∀ n, complexLexLE (ξ n) (η n))
    (hc : ∀ i j : ℤ, i < j → complexLexLE (η i) (ξ j))
    (i j : ℤ ×ₗ Fin 2) (hij : i ≤ j) :
    complexLexLE (periodicEndpointSlot ξ η i) (periodicEndpointSlot ξ η j) := by
  exact NLS.ordered_paired_slots complexLexLE ({(ofLex i).1,(ofLex j).1} : Finset ℤ) ξ η
    (fun n _ => hw n) (fun a _ b _ hab => hc a b hab)
    (ofLex i).1 (ofLex j).1 (by simp) (by simp) (ofLex i).2 (ofLex j).2 hij

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Analytic counts equal counts of selected central slot indices. -/
theorem PeriodicEndpointLabeling.analyticZeroCount_eq_card_filter_slots
    {hp : p ≠ ⊤} {φ : PairSpace p} {N : ℕ} {ξ η : ℤ → ℂ}
    (h : PeriodicEndpointLabeling hp φ N ξ η) (hp1 : 1 < p)
    (S : Set ℂ) (hS : ∀ z ∈ S, |z.re| ≤ centralCircleRadius N) :
    analyticZeroCount (canonicalPeriodicProduct hp φ) S =
      ((centralPeriodicSlots N).filter (fun k => periodicEndpointSlot ξ η k ∈ S)).card := by
  rw [h.analyticZeroCount_eq_sum_slots hp1 S hS]
  rw [Finset.card_filter]
  simp only [centralPeriodicSlots, Finset.sum_map, Finset.sum_product, Fin.sum_univ_two]
  rfl

end NLS.ZakharovShabat
