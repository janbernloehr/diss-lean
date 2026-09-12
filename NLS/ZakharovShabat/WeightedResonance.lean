import NLS.SequenceSpaces.WeightedPairMap

/-!
# The weighted resonant splitting in Section 6

The resonant projection selects physical frequencies `-n` and `n`. Both
projections are contractions for the source's finite-exponent pair norm.
-/

noncomputable section
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Retain exactly the scalar frequencies satisfying a predicate. -/
def weightedMask (w : Weight) (s : ℤ → Prop) [DecidablePred s] :
    WeightedCoeff w p →L[ℂ] WeightedCoeff w p :=
  WeightedCoeff.weightedMultiplierCLM w w (fun k => if s k then 1 else 0) 1 zero_le_one
    (fun k => by split_ifs <;> simp [le_of_lt (w.positive k)])

@[simp] theorem weightedMask_apply (w : Weight) (s : ℤ → Prop) [DecidablePred s]
    (a : WeightedCoeff w p) (k : ℤ) :
    (weightedMask w s a).val k = if s k then a.val k else 0 := by
  change (if s k then (1 : ℂ) else 0) * a.val k = _
  split_ifs <;> simp

theorem norm_weightedMask_le (w : Weight) (s : ℤ → Prop) [DecidablePred s]
    (a : WeightedCoeff w p) : ‖weightedMask w s a‖ ≤ ‖a‖ := by
  simpa only [one_mul] using! WeightedCoeff.norm_weightedMultiplier_le w w
    (fun k => if s k then 1 else 0) 1 zero_le_one
    (fun k => by split_ifs <;> simp [le_of_lt (w.positive k)]) a

/-- Projection onto `e_n^-` and `e_n^+`, in physical Fourier coordinates. -/
def resonantProjection (w : Weight) (n : ℤ) :
    WeightedCoeffPair w p →L[ℂ] WeightedCoeffPair w p :=
  WeightedCoeffPair.mapComponents w w (weightedMask w (· = -n)) (weightedMask w (· = n))

/-- Projection onto all modes complementary to the two resonant modes. -/
def complementaryProjection (w : Weight) (n : ℤ) :
    WeightedCoeffPair w p →L[ℂ] WeightedCoeffPair w p :=
  WeightedCoeffPair.mapComponents w w (weightedMask w (· ≠ -n)) (weightedMask w (· ≠ n))

@[simp] theorem resonantProjection_fst (w : Weight) (n : ℤ) (a : WeightedCoeffPair w p) (k : ℤ) :
    (resonantProjection w n a).fst.val k = if k = -n then a.fst.val k else 0 := weightedMask_apply _ _ _ _
@[simp] theorem resonantProjection_snd (w : Weight) (n : ℤ) (a : WeightedCoeffPair w p) (k : ℤ) :
    (resonantProjection w n a).snd.val k = if k = n then a.snd.val k else 0 := weightedMask_apply _ _ _ _
@[simp] theorem complementaryProjection_fst (w : Weight) (n : ℤ) (a : WeightedCoeffPair w p) (k : ℤ) :
    (complementaryProjection w n a).fst.val k = if k = -n then 0 else a.fst.val k := by
  change (weightedMask w (· ≠ -n) a.fst).val k = _
  rw [weightedMask_apply]; split_ifs <;> first | rfl | contradiction
@[simp] theorem complementaryProjection_snd (w : Weight) (n : ℤ) (a : WeightedCoeffPair w p) (k : ℤ) :
    (complementaryProjection w n a).snd.val k = if k = n then 0 else a.snd.val k := by
  change (weightedMask w (· ≠ n) a.snd).val k = _
  rw [weightedMask_apply]; split_ifs <;> first | rfl | contradiction

omit [Fact (1 ≤ p)] in
/-- Equality of pairs can be checked on their two raw coefficient sequences. -/
theorem weightedPair_ext {w : Weight} {a b : WeightedCoeffPair w p}
    (h₁ : ∀ k, a.fst.val k = b.fst.val k) (h₂ : ∀ k, a.snd.val k = b.snd.val k) : a = b :=
  (WithLp.ext_iff p).mpr (Prod.ext (Subtype.ext (funext h₁)) (Subtype.ext (funext h₂)))

theorem resonant_add_complementary (w : Weight) (n : ℤ) (a : WeightedCoeffPair w p) :
    resonantProjection w n a + complementaryProjection w n a = a := by
  apply weightedPair_ext <;> intro k
  · change (resonantProjection w n a).fst.val k + (complementaryProjection w n a).fst.val k = _
    simp only [resonantProjection_fst, complementaryProjection_fst]; split_ifs <;> simp
  · change (resonantProjection w n a).snd.val k + (complementaryProjection w n a).snd.val k = _
    simp only [resonantProjection_snd, complementaryProjection_snd]; split_ifs <;> simp

@[simp] theorem resonantProjection_idempotent (w : Weight) (n : ℤ) (a : WeightedCoeffPair w p) :
    resonantProjection w n (resonantProjection w n a) = resonantProjection w n a := by
  apply weightedPair_ext <;> intro k <;> simp <;> tauto

@[simp] theorem complementaryProjection_idempotent (w : Weight) (n : ℤ) (a : WeightedCoeffPair w p) :
    complementaryProjection w n (complementaryProjection w n a) = complementaryProjection w n a := by
  apply weightedPair_ext <;> intro k <;> simp <;> tauto

@[simp] theorem resonant_complementary_zero (w : Weight) (n : ℤ) (a : WeightedCoeffPair w p) :
    resonantProjection w n (complementaryProjection w n a) = 0 := by
  apply weightedPair_ext <;> intro k <;> simp <;> tauto

@[simp] theorem complementary_resonant_zero (w : Weight) (n : ℤ) (a : WeightedCoeffPair w p) :
    complementaryProjection w n (resonantProjection w n a) = 0 := by
  apply weightedPair_ext <;> intro k <;> simp <;> tauto

/-- Complementary vectors are exactly those with both resonant coefficients zero. -/
theorem complementaryProjection_eq_self_iff (w : Weight) (n : ℤ) (a : WeightedCoeffPair w p) :
    complementaryProjection w n a = a ↔ a.fst.val (-n) = 0 ∧ a.snd.val n = 0 := by
  constructor
  · intro h
    constructor
    · simpa using (congrArg (fun b => b.fst.val (-n)) h).symm
    · simpa using (congrArg (fun b => b.snd.val n) h).symm
  · rintro ⟨h₁, h₂⟩
    apply weightedPair_ext <;> intro k
    · by_cases hk : k = -n <;> simp [hk, h₁]
    · by_cases hk : k = n <;> simp [hk, h₂]

theorem norm_resonantProjection_le (hp : p ≠ ⊤) (w : Weight) (n : ℤ) (a : WeightedCoeffPair w p) :
    ‖resonantProjection w n a‖ ≤ ‖a‖ := by
  simpa only [one_mul] using! WeightedCoeffPair.norm_mapComponents_le hp w w
    (weightedMask w (· = -n)) (weightedMask w (· = n)) zero_le_one
    (fun a => by simpa using norm_weightedMask_le w (· = -n) a)
    (fun a => by simpa using norm_weightedMask_le w (· = n) a) a

theorem norm_complementaryProjection_le (hp : p ≠ ⊤) (w : Weight) (n : ℤ) (a : WeightedCoeffPair w p) :
    ‖complementaryProjection w n a‖ ≤ ‖a‖ := by
  simpa only [one_mul] using! WeightedCoeffPair.norm_mapComponents_le hp w w
    (weightedMask w (· ≠ -n)) (weightedMask w (· ≠ n)) zero_le_one
    (fun a => by simpa using norm_weightedMask_le w (· ≠ -n) a)
    (fun a => by simpa using norm_weightedMask_le w (· ≠ n) a) a

end NLS.ZakharovShabat
