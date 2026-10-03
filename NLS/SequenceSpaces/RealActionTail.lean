import NLS.SequenceSpaces.RealActionReduction
import NLS.SequenceSpaces.RealCoeffTruncation

/-! # Small finite actions and a fixed summable tail

For a target in any finite real sequence exponent, sufficiently small
actions on a suitable finite set, together with the original outside
coordinates, give a small target in that same exponent. The candidate
may initially be given in a different exponent space.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.RealCoeff
variable {p q : ℝ≥0∞}

/-- Transfer finitely many coordinate pairs into any sequence exponent. -/
def finitePair (p : ℝ≥0∞) (A : Finset ℤ) (z : RealCoeff q × RealCoeff q) :
    RealCoeff p × RealCoeff p :=
  (∑ n ∈ A, lp.single (E := fun _ : ℤ => ℝ) p n (z.1 n),∑ n ∈ A, lp.single (E := fun _ : ℤ => ℝ) p n (z.2 n))

@[simp] theorem finitePair_apply (A : Finset ℤ) (z : RealCoeff q × RealCoeff q) (n : ℤ) :
    (finitePair p A z).1 n = (if n ∈ A then z.1 n else 0) ∧
    (finitePair p A z).2 n = (if n ∈ A then z.2 n else 0) := by
  have he (a : RealCoeff q) :
      (∑ i ∈ A, lp.single (E := fun _ : ℤ => ℝ) p i (a i)) n =
        if n ∈ A then a n else 0 := by
    change (lp.evalₗ (𝕜 := ℝ) (fun _ : ℤ => ℝ) p n) (∑ i ∈ A, lp.single p i (a i)) = _
    rw [map_sum]
    simp [lp.evalₗ_apply,lp.single_apply,Pi.single_apply]
  exact ⟨he z.1,he z.2⟩

/-- A bound on each quadratic action bounds the norm of its finite block. -/
theorem norm_finitePair_le [Fact (1 ≤ p)] (A : Finset ℤ) (z : RealCoeff q × RealCoeff q)
    {c : ℝ} (hc : 0 < c) (h : ∀ n ∈ A, pairAction z n < c^2/2) :
    ‖finitePair p A z‖ ≤ A.card*c := by
  have hcoords (n : ℤ) (hn : n ∈ A) : |z.1 n| ≤ c ∧ |z.2 n| ≤ c := by
    have hi := h n hn
    dsimp only [pairAction] at hi
    constructor <;> apply le_of_lt <;> apply abs_lt.mpr
    · constructor <;> nlinarith [sq_nonneg (z.2 n)]
    · constructor <;> nlinarith [sq_nonneg (z.1 n)]
  have hp0 : 0 < p := zero_lt_one.trans_le (Fact.out : 1 ≤ p)
  change max ‖∑ n ∈ A, lp.single (E := fun _ : ℤ => ℝ) p n (z.1 n)‖ ‖∑ n ∈ A, lp.single (E := fun _ : ℤ => ℝ) p n (z.2 n)‖ ≤ _
  apply max_le
  · calc
      _ ≤ ∑ n ∈ A, ‖lp.single (E := fun _ : ℤ => ℝ) p n (z.1 n)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ A, c := Finset.sum_le_sum (fun n hn => by
        rw [lp.norm_single hp0,Real.norm_eq_abs]; exact (hcoords n hn).1)
      _ = A.card*c := by simp
  · calc
      _ ≤ ∑ n ∈ A, ‖lp.single (E := fun _ : ℤ => ℝ) p n (z.2 n)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ A, c := Finset.sum_le_sum (fun n hn => by
        rw [lp.norm_single hp0,Real.norm_eq_abs]; exact (hcoords n hn).2)
      _ = A.card*c := by simp

/-- Small finitely many actions and the unchanged original tail imply a
small norm in the original finite exponent, even for a candidate initially
given only in a different exponent. -/
theorem exists_finite_action_small_norm [Fact (1 ≤ p)] (hp : p ≠ ⊤)
    (z : RealCoeff p × RealCoeff p) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : Finset ℤ, ∃ δ : ℝ, 0 < δ ∧
      ∀ {q : ℝ≥0∞} (w : RealCoeff q × RealCoeff q),
        (∀ n ∉ A, w.1 n = z.1 n ∧ w.2 n = z.2 n) →
        (∀ n ∈ A, pairAction w n < δ) →
        ∃ y : RealCoeff p × RealCoeff p, ‖y‖ < ε ∧
          ∀ n : ℤ, y.1 n = w.1 n ∧ y.2 n = w.2 n := by
  have ht : Tendsto (fun A : Finset ℤ => ‖z-truncatePair A z‖) atTop (𝓝 0) := by
    have hh : Tendsto (fun A : Finset ℤ => z-truncatePair A z) atTop (𝓝 (z-z)) :=
      tendsto_const_nhds.sub (tendsto_truncatePair hp z)
    simpa using hh.norm
  obtain ⟨A,hA⟩ := ((tendsto_order.mp ht).2 (ε/2) (half_pos hε)).exists
  let c : ℝ := ε/(2*(A.card+1))
  have hc : 0 < c := div_pos hε (by positivity)
  have hcard : (A.card : ℝ)*c < ε/2 := by
    have he : c*(2*(A.card+1)) = ε := by dsimp [c]; field_simp
    nlinarith
  refine ⟨A,c^2/2,by positivity,?_⟩
  intro q w hout hsmall
  let y := z-truncatePair A z+finitePair p A w
  refine ⟨y,?_,fun n => ?_⟩
  · exact (norm_add_le _ _).trans_lt
      (add_lt_add hA ((norm_finitePair_le A w hc hsmall).trans_lt hcard)) |>.trans_eq (by ring)
  · change z.1 n-truncate A z.1 n+(finitePair p A w).1 n = w.1 n ∧
      z.2 n-truncate A z.2 n+(finitePair p A w).2 n = w.2 n
    rw [(finitePair_apply A w n).1,(finitePair_apply A w n).2]
    by_cases hn : n ∈ A
    · simp [hn]
    · simpa only [truncate_apply,hn,ite_false,sub_zero,add_zero] using
        ⟨(hout n hn).1.symm,(hout n hn).2.symm⟩

end NLS.RealCoeff
