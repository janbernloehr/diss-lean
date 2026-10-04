import NLS.SequenceSpaces.Multiplier
import NLS.SequenceSpaces.RealFormIdentity

/-! # Arbitrary coordinate sign changes

Changing any set of signs is a complex linear isometry of lp. It
preserves real coordinates and the square of every coordinate. Infinite
sign selections are permitted, with no approximation or finite-support
hypothesis.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

private def signSymbol (e : ℤ → Bool) : Coeff ⊤ :=
  ⟨fun n => if e n then -1 else 1,memℓp_infty ⟨1,by
    rintro _ ⟨n,rfl⟩
    cases h : e n <;> simp [h]⟩⟩

/-- Change the sign at every selected index, as a bounded complex linear map. -/
def signChange (e : ℤ → Bool) : Coeff p →L[ℂ] Coeff p := multiplierCLM (signSymbol e)

@[simp] theorem signChange_apply (e : ℤ → Bool) (a : Coeff p) (n : ℤ) :
    signChange e a n = if e n then -a n else a n := by
  change (if e n then (-1:ℂ) else 1)*a n = _
  cases e n <;> simp

@[simp] theorem norm_signChange_apply (e : ℤ → Bool) (a : Coeff p) (n : ℤ) :
    ‖signChange e a n‖ = ‖a n‖ := by
  cases h : e n <;> simp [h]

@[simp] theorem signChange_sq (e : ℤ → Bool) (a : Coeff p) (n : ℤ) :
    signChange e a n ^ 2 = a n ^ 2 := by
  cases h : e n <;> simp [h]

@[simp] theorem signChange_involutive (e : ℤ → Bool) (a : Coeff p) :
    signChange e (signChange e a) = a := by
  ext n
  cases h : e n <;> simp [h]

@[simp] theorem norm_signChange (e : ℤ → Bool) (a : Coeff p) : ‖signChange e a‖ = ‖a‖ := by
  apply le_antisymm
  · exact lp.norm_mono (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)))
      (fun n => (norm_signChange_apply e a n).le)
  · exact lp.norm_mono (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p)))
      (fun n => (norm_signChange_apply e a n).ge)

/-- Equal coordinate squares differ by one (possibly infinite) sign selection. -/
theorem exists_signChange_of_sq_eq (a b : Coeff p) (h : ∀ n, a n ^ 2 = b n ^ 2) :
    ∃ e : ℤ → Bool, signChange e a = b := by
  classical
  have he (n : ℤ) : ∃ e : Bool, (if e then -a n else a n) = b n := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (h n) with hn | hn
    · exact ⟨false,hn⟩
    · exact ⟨true,by simp [hn]⟩
  choose e he using he
  refine ⟨e,?_⟩
  ext n
  rw [signChange_apply]
  exact he n

/-- Square-root choices agreeing on a finite head differ by tail signs only. -/
theorem exists_signChange_of_sq_eq_on_complement (S : Finset ℤ) (a b : Coeff p)
    (hsq : ∀ n, a n^2 = b n^2) (hhead : ∀ n ∈ S, a n = b n) :
    ∃ e : ℤ → Bool, (∀ n ∈ S, e n = false) ∧ signChange e a = b := by
  classical
  let e : ℤ → Bool := fun n => decide (a n ≠ b n)
  refine ⟨e,fun n hn => by simp [e,hhead n hn],?_⟩
  ext n
  rw [signChange_apply]
  by_cases he : a n = b n
  · simp [e,he]
  · have hn : a n = -b n := (sq_eq_sq_iff_eq_or_eq_neg.mp (hsq n)).resolve_left he
    simp [e,hn]

/-- Independent signs in the two Birkhoff components. -/
def pairSignChange (e d : ℤ → Bool) :
    (Coeff p × Coeff p) →L[ℂ] (Coeff p × Coeff p) := (signChange e).prodMap (signChange d)

@[simp] theorem norm_pairSignChange (e d : ℤ → Bool) (z : Coeff p × Coeff p) :
    ‖pairSignChange e d z‖ = ‖z‖ := by
  simp [pairSignChange,Prod.norm_def]

theorem pairSignChange_mem_realPairLocus (e d : ℤ → Bool) (z : Coeff p × Coeff p)
    (hz : z ∈ realPairLocus p) : pairSignChange e d z ∈ realPairLocus p := by
  constructor <;> intro n
  · change (signChange e z.1 n).im = 0
    cases h : e n <;> simp [h,hz.1 n]
  · change (signChange d z.2 n).im = 0
    cases h : d n <;> simp [h,hz.2 n]

/-- Every individual quadratic action is unchanged. -/
theorem pairSignChange_action (e d : ℤ → Bool) (z : Coeff p × Coeff p) (n : ℤ) :
    (pairSignChange e d z).1 n ^ 2+(pairSignChange e d z).2 n ^ 2 = z.1 n ^ 2+z.2 n ^ 2 := by
  change signChange e z.1 n ^ 2+signChange d z.2 n ^ 2 = _
  simp

/-- A sign change fixing a center preserves its entire complex ball. -/
theorem pairSignChange_mem_ball (e d : ℤ → Bool) (c z : Coeff p × Coeff p)
    (hc : pairSignChange e d c = c) (r : ℝ) :
    pairSignChange e d z ∈ ball c r ↔ z ∈ ball c r := by
  simp only [mem_ball,dist_eq_norm]
  have hd : ‖pairSignChange e d z-c‖ = ‖z-c‖ := by
    calc
      _ = ‖pairSignChange e d z-pairSignChange e d c‖ := by rw [hc]
      _ = ‖z-c‖ := by rw [← map_sub,norm_pairSignChange]
  rw [hd]

end NLS.Coeff
