import NLS.ZakharovShabat.SourceHilbertAngleDisplacement

/-! # Finite successive action reductions

A list of indexed times acts by the actual Hilbert angle flow. Admissibility
requires each time to be nonnegative and strictly before that step's collapse.
Every finite admissible sequence has a displacement in each finite source
exponent above one. Prescribed positive bounds on finitely many actions can
be attained by such a sequence while retaining every outside coordinate.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- Apply the actual angle-flow moves in list order. -/
def hilbertActionReductionSequence
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (moves : List (ℤ × ℝ)) : realTypeSourceSubmodule 2 :=
  moves.foldl (fun ψ move => D.hilbertActionReduction ψ move.1 move.2) φ

@[simp] theorem hilbertActionReductionSequence_nil
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) : D.hilbertActionReductionSequence φ [] = φ := rfl

@[simp] theorem hilbertActionReductionSequence_cons
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (move : ℤ × ℝ) (moves : List (ℤ × ℝ)) :
    D.hilbertActionReductionSequence φ (move :: moves) =
      D.hilbertActionReductionSequence (D.hilbertActionReduction φ move.1 move.2) moves := rfl

@[simp] theorem hilbertActionReductionSequence_append_singleton
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (moves : List (ℤ × ℝ)) (k : ℤ) (t : ℝ) :
    D.hilbertActionReductionSequence φ (moves ++ [(k,t)]) =
      D.hilbertActionReduction (D.hilbertActionReductionSequence φ moves) k t := by
  simp [hilbertActionReductionSequence,List.foldl_append]

/-- Each successive move stops before its own current action vanishes. -/
def AdmissibleActionReductions
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) : List (ℤ × ℝ) → Prop
  | [] => True
  | move :: moves => 0 ≤ move.2 ∧
      move.2 < (sourceRealAction (by simp) (by norm_num) φ.val φ.property move.1).re ∧
      D.AdmissibleActionReductions (D.hilbertActionReduction φ move.1 move.2) moves

theorem admissibleActionReductions_append_singleton
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (moves : List (ℤ × ℝ)) (k : ℤ) (t : ℝ)
    (hm : D.AdmissibleActionReductions φ moves) (ht : 0 ≤ t)
    (ha : t < (sourceRealAction (by simp) (by norm_num)
      (D.hilbertActionReductionSequence φ moves).val
      (D.hilbertActionReductionSequence φ moves).property k).re) :
    D.AdmissibleActionReductions φ (moves ++ [(k,t)]) := by
  induction moves generalizing φ with
  | nil => exact ⟨ht,ha,True.intro⟩
  | cons move moves ih => exact ⟨hm.1,hm.2.1,ih _ hm.2.2 ha⟩

/-- Every unselected rectangular coordinate is retained, not merely its action. -/
theorem hilbertActionReductionSequence_coordinates_of_not_selected
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (moves : List (ℤ × ℝ)) (n : ℤ)
    (hn : ∀ move ∈ moves, n ≠ move.1) :
    (D.hilbertRealHomeomorph (D.hilbertActionReductionSequence φ moves)).1 n =
      (D.hilbertRealHomeomorph φ).1 n ∧
    (D.hilbertRealHomeomorph (D.hilbertActionReductionSequence φ moves)).2 n =
      (D.hilbertRealHomeomorph φ).2 n := by
  induction moves generalizing φ with
  | nil => exact ⟨rfl,rfl⟩
  | cons move moves ih =>
    have htail := ih (D.hilbertActionReduction φ move.1 move.2)
      (fun m hm => hn m (List.mem_cons_of_mem _ hm))
    have hfirst := RealCoeff.actionReduction_apply_ne (D.hilbertRealHomeomorph φ) move.1 n
      (hn move (List.mem_cons_self ..)) move.2
    rw [← D.hilbertRealHomeomorph_actionReduction] at hfirst
    exact ⟨htail.1.trans hfirst.1,htail.2.trans hfirst.2⟩

/-- Summing the stronger-space displacements along an admissible list
recovers both Fourier components of the total original source displacement. -/
theorem hilbertActionReductionSequence_displacement
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (moves : List (ℤ × ℝ))
    (hm : D.AdmissibleActionReductions φ moves) :
    ∃ d : realTypeSourceSubmodule p, ∀ n : ℤ,
      d.val.fst n = (D.hilbertActionReductionSequence φ moves).val.fst n-φ.val.fst n ∧
      d.val.snd n = (D.hilbertActionReductionSequence φ moves).val.snd n-φ.val.snd n := by
  induction moves generalizing φ with
  | nil => exact ⟨0,fun n => by simp⟩
  | cons move moves ih =>
    have ha := lt_of_le_of_lt hm.1 hm.2.1
    obtain ⟨d₁,_,_,hd₁⟩ := D.hilbert_angleFlow_continuous_real_displacement hp hp1 move.1 φ ha
    obtain ⟨d₂,hd₂⟩ := ih (D.hilbertActionReduction φ move.1 move.2) hm.2.2
    refine ⟨d₁ ⟨move.2,hm.2.1⟩+d₂,fun n => ?_⟩
    have h₁ := hd₁ ⟨move.2,hm.2.1⟩ n
    have h₂ := hd₂ n
    change (d₁ ⟨move.2,hm.2.1⟩).val.fst n+d₂.val.fst n = _ ∧
      (d₁ ⟨move.2,hm.2.1⟩).val.snd n+d₂.val.snd n = _
    rw [h₁.1,h₂.1,h₁.2,h₂.2]
    constructor <;> dsimp only [hilbertActionReductionSequence_cons] <;> ring

/-- For exponents at most two, the recovered displacement includes into
Hilbert space as literal equality of source elements. -/
theorem hilbertActionReductionSequence_displacement_inclusion
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (moves : List (ℤ × ℝ))
    (hm : D.AdmissibleActionReductions φ moves) :
    ∃ d : realTypeSourceSubmodule p, CoeffPair.exponentInclusion hp2 d.val =
      (D.hilbertActionReductionSequence φ moves).val-φ.val := by
  obtain ⟨d,hd⟩ := D.hilbertActionReductionSequence_displacement hp hp1 φ moves hm
  refine ⟨d,?_⟩
  apply (CoeffPair.toMax 2).injective
  apply Prod.ext <;> ext n
  · exact (hd n).1
  · exact (hd n).2

/-- A finite admissible reduction cannot change whether the Hilbert
source belongs to a stronger exponent space. -/
theorem hilbertActionReductionSequence_mem_exponent_iff
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2)
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (moves : List (ℤ × ℝ))
    (hm : D.AdmissibleActionReductions φ moves) :
    (∃ ψ : realTypeSourceSubmodule p, CoeffPair.exponentInclusion hp2 ψ.val =
      (D.hilbertActionReductionSequence φ moves).val) ↔
    ∃ ψ : realTypeSourceSubmodule p, CoeffPair.exponentInclusion hp2 ψ.val = φ.val := by
  obtain ⟨d,hd⟩ := D.hilbertActionReductionSequence_displacement_inclusion hp hp1 hp2 φ moves hm
  constructor
  · rintro ⟨ψ,hψ⟩
    refine ⟨ψ-d,?_⟩
    change CoeffPair.exponentInclusion hp2 (ψ.val-d.val) = φ.val
    rw [map_sub,hψ,hd]
    abel
  · rintro ⟨ψ,hψ⟩
    refine ⟨ψ+d,?_⟩
    change CoeffPair.exponentInclusion hp2 (ψ.val+d.val) = _
    rw [map_add,hψ,hd]
    abel

/-- None of the original spectral actions increases under an admissible list. -/
theorem hilbertActionReductionSequence_action_le
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (moves : List (ℤ × ℝ))
    (hm : D.AdmissibleActionReductions φ moves) (n : ℤ) :
    (sourceRealAction (by simp) (by norm_num) (D.hilbertActionReductionSequence φ moves).val
      (D.hilbertActionReductionSequence φ moves).property n).re ≤
      (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re := by
  induction moves generalizing φ with
  | nil => exact le_rfl
  | cons move moves ih =>
    have hfirst : (sourceRealAction (by simp) (by norm_num)
        (D.hilbertActionReduction φ move.1 move.2).val
        (D.hilbertActionReduction φ move.1 move.2).property n).re ≤
        (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re := by
      by_cases hn : n = move.1
      · subst n
        rw [D.hilbertActionReduction_action_same φ move.1 (lt_of_le_of_lt hm.1 hm.2.1) move.2 hm.2.1.le]
        exact sub_le_self _ hm.1
      · exact le_of_eq (D.hilbertActionReduction_action_ne φ move.1 n hn move.2)
    exact (ih (D.hilbertActionReduction φ move.1 move.2) hm.2.2).trans hfirst

/-- Finitely many prescribed positive action bounds are attained by actual
admissible angle-flow moves. Every unselected coordinate is retained and
the total source displacement belongs to every finite exponent above one.
Already small actions, including collapsed gaps, require no move. -/
theorem exists_hilbertActionReductionSequence_small_actions
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (A : Finset ℤ) (ε : ℤ → ℝ)
    (hε : ∀ n ∈ A, 0 < ε n) :
    ∃ moves : List (ℤ × ℝ), D.AdmissibleActionReductions φ moves ∧
      (∀ move ∈ moves, move.1 ∈ A) ∧
      (∀ n ∈ A, (sourceRealAction (by simp) (by norm_num)
        (D.hilbertActionReductionSequence φ moves).val
        (D.hilbertActionReductionSequence φ moves).property n).re < ε n) ∧
      (∀ n ∉ A,
        (D.hilbertRealHomeomorph (D.hilbertActionReductionSequence φ moves)).1 n =
          (D.hilbertRealHomeomorph φ).1 n ∧
        (D.hilbertRealHomeomorph (D.hilbertActionReductionSequence φ moves)).2 n =
          (D.hilbertRealHomeomorph φ).2 n) ∧
      ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ → 1 < p →
        ∃ d : realTypeSourceSubmodule p, ∀ n : ℤ,
          d.val.fst n = (D.hilbertActionReductionSequence φ moves).val.fst n-φ.val.fst n ∧
          d.val.snd n = (D.hilbertActionReductionSequence φ moves).val.snd n-φ.val.snd n := by
  classical
  let I (ψ : realTypeSourceSubmodule 2) (n : ℤ) :=
    (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n).re
  suffices ∃ moves : List (ℤ × ℝ), D.AdmissibleActionReductions φ moves ∧
      (∀ move ∈ moves, move.1 ∈ A) ∧
      ∀ n ∈ A, I (D.hilbertActionReductionSequence φ moves) n < ε n by
    obtain ⟨moves,hm,hsel,hsmall⟩ := this
    refine ⟨moves,hm,hsel,hsmall,?_,?_⟩
    · intro n hn
      apply D.hilbertActionReductionSequence_coordinates_of_not_selected
      intro move hmove heq
      exact hn (heq ▸ hsel move hmove)
    · intro p _ hp hp1
      exact D.hilbertActionReductionSequence_displacement hp hp1 φ moves hm
  induction A using Finset.induction with
  | empty => exact ⟨[],True.intro,by simp,by simp⟩
  | @insert k A hk ih =>
    obtain ⟨moves,hm,hsel,hsmall⟩ := ih (fun n hn => hε n (Finset.mem_insert_of_mem hn))
    let ψ := D.hilbertActionReductionSequence φ moves
    by_cases hsmallk : I ψ k < ε k
    · refine ⟨moves,hm,fun move hmove => Finset.mem_insert_of_mem (hsel move hmove),?_⟩
      intro n hn
      rcases Finset.mem_insert.mp hn with rfl | hn
      · exact hsmallk
      · exact hsmall n hn
    · have ha : 0 < I ψ k := lt_of_lt_of_le (hε k (Finset.mem_insert_self ..)) (le_of_not_gt hsmallk)
      obtain ⟨t,ht,hta,_,hnew,hothers⟩ := D.exists_hilbertActionReduction_small_action ψ k ha
        (ε k) (hε k (Finset.mem_insert_self ..))
      refine ⟨moves ++ [(k,t)],D.admissibleActionReductions_append_singleton φ moves k t hm ht hta,?_,?_⟩
      · intro move hmove
        rcases List.mem_append.mp hmove with hmove | hmove
        · exact Finset.mem_insert_of_mem (hsel move hmove)
        · have heq : move = (k,t) := List.mem_singleton.mp hmove
          subst move
          exact Finset.mem_insert_self ..
      · intro n hn
        rw [D.hilbertActionReductionSequence_append_singleton]
        rcases Finset.mem_insert.mp hn with rfl | hn
        · exact hnew
        · have hnk : n ≠ k := by intro heq; exact hk (heq ▸ hn)
          exact (hothers n hnk).trans_lt (hsmall n hn)

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
