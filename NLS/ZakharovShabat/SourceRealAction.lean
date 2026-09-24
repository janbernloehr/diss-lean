import NLS.ZakharovShabat.SourceActionMidpointCircleExistence

/-!
# Indexed actions at real-type sources

The action on sufficiently small midpoint circles is constant. We
select one such circle to define an indexed action at a real-type
source, prove independence within the stable radius range, and record
the nonnegative sign and collapsed-gap zero criterion.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A chosen radius range on which midpoint-circle actions agree. -/
def sourceRealActionEpsilon
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) : ℝ :=
  Classical.choose
    (exists_sourceActionCircle_eq_of_small_midpointCircles hp hp1 ψ hreal n)

/-- The chosen radius range is positive and all its midpoint circles
have the same action. -/
theorem sourceRealActionEpsilon_spec
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
    let d : ℝ := (r.re-l.re)/2
    0 < sourceRealActionEpsilon hp hp1 ψ hreal n ∧
      ∀ η₁ ∈ Ioc 0 (sourceRealActionEpsilon hp hp1 ψ hreal n),
        ∀ η₂ ∈ Ioc 0 (sourceRealActionEpsilon hp hp1 ψ hreal n),
          sourceActionCircle hp hp1 ψ c (d+η₁) =
            sourceActionCircle hp hp1 ψ c (d+η₂) :=
  Classical.choose_spec
    (exists_sourceActionCircle_eq_of_small_midpointCircles hp hp1 ψ hreal n)

/-- The action indexed by a real periodic gap, evaluated on a
midpoint circle inside its stable range. -/
def sourceRealAction
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) : ℂ :=
  let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
    (periodOnePotential_mem ψ) n
  let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
  let d : ℝ := (r.re-l.re)/2
  sourceActionCircle hp hp1 ψ c
    (d+sourceRealActionEpsilon hp hp1 ψ hreal n/2)

/-- Every circle within the chosen stable range computes the same
indexed real-source action. -/
theorem sourceRealAction_eq_small_midpointCircle
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ)
    {η : ℝ}
    (hη : η ∈ Ioc 0 (sourceRealActionEpsilon hp hp1 ψ hreal n)) :
    let l := canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let r := canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
      (periodOnePotential_mem ψ) n
    let c : ℂ := (((l.re+r.re)/2:ℝ):ℂ)
    let d : ℝ := (r.re-l.re)/2
    sourceRealAction hp hp1 ψ hreal n =
      sourceActionCircle hp hp1 ψ c (d+η) := by
  let ε := sourceRealActionEpsilon hp hp1 ψ hreal n
  have hspec := sourceRealActionEpsilon_spec hp hp1 ψ hreal n
  have hmid : ε/2 ∈ Ioc 0 ε := by
    constructor <;> dsimp [ε] at * <;> linarith [hspec.1]
  change sourceActionCircle hp hp1 ψ
      ((((canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re +
        (canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)/2:ℝ):ℂ)
      (((canonicalPeriodicRight hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re -
        (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n).re)/2 + ε/2) = _
  exact hspec.2 (ε/2) hmid η hη

/-- The indexed action at every real-type source is real and
nonnegative; it vanishes exactly when the selected gap collapses. -/
theorem sourceRealAction_nonneg_and_eq_zero_iff_gap_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    0 ≤ (sourceRealAction hp hp1 ψ hreal n).re ∧
      (sourceRealAction hp hp1 ψ hreal n).im = 0 ∧
      (sourceRealAction hp hp1 ψ hreal n = 0 ↔
        sourcePeriodicGapDisplacement hp hp1 ψ n = 0) := by
  let ε := sourceRealActionEpsilon hp hp1 ψ hreal n
  obtain ⟨δ,hδ,hchar⟩ :=
    exists_sourceActionCircle_nonneg_and_zero_iff_gap_zero_midpoint
      hp hp1 ψ hreal n
  let η : ℝ := min ε δ/2
  have hε : 0 < ε :=
    (sourceRealActionEpsilon_spec hp hp1 ψ hreal n).1
  have hη : 0 < η := by
    dsimp [η]
    exact div_pos (lt_min hε hδ) (by norm_num)
  have hηε : η ∈ Ioc 0 ε := by
    constructor
    · exact hη
    · dsimp [η]
      linarith [min_le_left ε δ]
  have hηδ : η ∈ Ioc 0 δ := by
    constructor
    · exact hη
    · dsimp [η]
      linarith [min_le_right ε δ]
  rw [sourceRealAction_eq_small_midpointCircle hp hp1 ψ hreal n hηε]
  exact hchar η hηδ

end NLS.ZakharovShabat
