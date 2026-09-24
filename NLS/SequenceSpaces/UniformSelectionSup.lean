import NLS.SequenceSpaces.Basic

/-!
# Coordinate suprema from uniform bounds on independent selections

If every choice of one point from each coordinate set produces an `ℓp`
sequence with a common norm bound, then the coordinatewise supremum is
itself an `ℓp` sequence with the same bound.  The proof selects values
arbitrarily close to each powered coordinate supremum and tests finite
sums before taking the approximation error to zero.
-/

noncomputable section
open scoped ENNReal
namespace NLS

/-- Uniform `ℓp` bounds for all independent selections control the
sequence of coordinatewise suprema at finite positive exponent. -/
theorem exists_uniformSelectionSup
    {X : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (S : Set ℤ) (D : ℤ → Set X)
    (hD : ∀ n, (D n).Nonempty) (F : ℤ → X → ℂ)
    (K : ℝ) (hK : 0 ≤ K)
    (hsel : ∀ z : ℤ → X, (∀ n, z n ∈ D n) →
      ∃ b : Coeff p, (∀ n ∈ S, b n = F n (z n)) ∧ ‖b‖ ≤ K) :
    ∃ B : Coeff p,
      (∀ n ∈ S, ∀ x ∈ D n, ‖F n x‖ ≤ ‖B n‖) ∧
      (∀ n ∈ S, ∀ t : ℝ, 0 ≤ t →
        (∀ x ∈ D n, ‖F n x‖ ≤ t) → ‖B n‖ ≤ t) ∧
      (∀ n ∉ S, B n = 0) ∧ ‖B‖ ≤ K := by
  classical
  let r := p.toReal
  have hr : 0 < r := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  let U (n : ℤ) : Set ℝ := {u | ∃ x ∈ D n, u = ‖F n x‖^r}
  have hUne (n : ℤ) : (U n).Nonempty := by
    obtain ⟨x,hx⟩ := hD n
    exact ⟨‖F n x‖^r,x,hx,rfl⟩
  have hUb (n : ℤ) (hn : n ∈ S) : BddAbove (U n) := by
    refine ⟨K^r, ?_⟩
    intro u hu
    obtain ⟨x,hx,rfl⟩ := hu
    let z : ℤ → X := fun i => if i = n then x else Classical.choose (hD i)
    have hz (i : ℤ) : z i ∈ D i := by
      by_cases hi : i = n
      · subst i
        simpa [z] using hx
      · simpa [z, hi] using (Classical.choose_spec (hD i))
    obtain ⟨b,hb,hbK⟩ := hsel z hz
    have hbn : b n = F n x := by simpa [z] using hb n hn
    calc
      ‖F n x‖^r = ‖b n‖^r := by rw [hbn]
      _ ≤ ‖b‖^r := Real.rpow_le_rpow (norm_nonneg _)
        (lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) b n) hr.le
      _ ≤ K^r := Real.rpow_le_rpow (norm_nonneg _) hbK hr.le
  let v (n : ℤ) : ℝ := if n ∈ S then sSup (U n) else 0
  have hv0 (n : ℤ) : 0 ≤ v n := by
    by_cases hn : n ∈ S
    · obtain ⟨u,hu⟩ := hUne n
      rcases hu with ⟨x,hx,rfl⟩
      exact (Real.rpow_nonneg (norm_nonneg _) _).trans
        (by simpa [v, hn] using (le_csSup (hUb n hn) (show ‖F n x‖^r ∈ U n from ⟨x,hx,rfl⟩)))
    · simp [v, hn]
  have hApprox (δ : ℝ) (hδ : 0 < δ) :
      ∃ z : ℤ → X, (∀ n, z n ∈ D n) ∧
        ∀ n : ℤ, v n ≤ ‖F n (z n)‖^r+δ := by
    have hpoint (n : ℤ) :
        ∃ x ∈ D n, v n ≤ ‖F n x‖^r+δ := by
      by_cases hn : n ∈ S
      · have hlt : v n-δ < sSup (U n) := by simp [v, hn]; linarith
        obtain ⟨u,hu,hu'⟩ := exists_lt_of_lt_csSup (hUne n) hlt
        obtain ⟨x,hx,rfl⟩ := hu
        exact ⟨x,hx,by linarith⟩
      · obtain ⟨x,hx⟩ := hD n
        refine ⟨x,hx,?_⟩
        simp only [v, if_neg hn]
        positivity
    let z (n : ℤ) := Classical.choose (hpoint n)
    exact ⟨z,fun n => (Classical.choose_spec (hpoint n)).1,
      fun n => (Classical.choose_spec (hpoint n)).2⟩
  have hSumδ (s : Finset ℤ) (δ : ℝ) (hδ : 0 < δ) :
      ∑ n ∈ s, v n ≤ K^r+(s.card:ℝ)*δ := by
    obtain ⟨z,hz,happrox⟩ := hApprox δ hδ
    obtain ⟨b,hb,hbK⟩ := hsel z hz
    calc
      ∑ n ∈ s, v n ≤ ∑ n ∈ s, (‖b n‖^r+δ) := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hnS : n ∈ S
        · simpa only [← hb n hnS] using happrox n
        · have hv : v n = 0 := by simp [v, hnS]
          rw [hv]
          positivity
      _ = (∑ n ∈ s, ‖b n‖^r)+(s.card:ℝ)*δ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ‖b‖^r+(s.card:ℝ)*δ :=
        add_le_add (lp.sum_rpow_le_norm_rpow hr b s) le_rfl
      _ ≤ K^r+(s.card:ℝ)*δ :=
        add_le_add (Real.rpow_le_rpow (norm_nonneg _) hbK hr.le) le_rfl
  have hSum (s : Finset ℤ) : ∑ n ∈ s, v n ≤ K^r := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let δ := ε/((s.card:ℝ)+1)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hc : (s.card:ℝ)*δ ≤ ε := by
      dsimp [δ]
      calc
        (s.card:ℝ)*(ε/((s.card:ℝ)+1)) =
            ((s.card:ℝ)*ε)/((s.card:ℝ)+1) := by ring
        _ ≤ ε := (div_le_iff₀ (by positivity : 0 < (s.card:ℝ)+1)).mpr
          (by nlinarith [Nat.cast_nonneg (α := ℝ) s.card])
    exact (hSumδ s δ hδ).trans (add_le_add le_rfl hc)
  have hpow (n : ℤ) :
      ‖(((v n)^(1/r) : ℝ) : ℂ)‖^r = v n := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (hv0 n) _), ← Real.rpow_mul (hv0 n)]
    rw [show (1/r)*r = 1 by field_simp, Real.rpow_one]
  have hfinite (s : Finset ℤ) :
      ∑ n ∈ s, ‖(((v n)^(1/r) : ℝ) : ℂ)‖^r ≤ K^r := by
    calc
      _ = ∑ n ∈ s, v n := by
        apply Finset.sum_congr rfl
        intro n _
        exact hpow n
      _ ≤ _ := hSum s
  let B : Coeff p := ⟨fun n => (((v n)^(1/r) : ℝ) : ℂ),
    (memℓp_gen' (C := K^r) (fun s => by
      change ∑ n ∈ s, ‖(((v n)^(1/r) : ℝ) : ℂ)‖^r ≤ K^r
      exact hfinite s))⟩
  have hBn (n : ℤ) : ‖B n‖^r = v n := hpow n
  have hBnorm : ‖B‖ ≤ K := by
    apply lp.norm_le_of_forall_sum_le hr hK
    intro s
    change ∑ n ∈ s, ‖B n‖^r ≤ K^r
    calc
      _ = ∑ n ∈ s, v n := by
        apply Finset.sum_congr rfl
        intro n _
        exact hBn n
      _ ≤ _ := hSum s
  refine ⟨B,?_,?_,?_,hBnorm⟩
  · intro n hn x hx
    have hxpow : ‖F n x‖^r ≤ ‖B n‖^r := by
      rw [hBn]
      simp only [v, if_pos hn]
      exact le_csSup (hUb n hn) ⟨x,hx,rfl⟩
    exact (Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hr).mp hxpow
  · intro n hn t ht hupper
    have hpowupper : ‖B n‖^r ≤ t^r := by
      rw [hBn]
      simp only [v, if_pos hn]
      apply csSup_le (hUne n)
      intro u hu
      obtain ⟨x,hx,rfl⟩ := hu
      exact Real.rpow_le_rpow (norm_nonneg _) (hupper x hx) hr.le
    exact (Real.rpow_le_rpow_iff (norm_nonneg _) ht hr).mp hpowupper
  · intro n hn
    have hv : v n = 0 := by simp [v, hn]
    change (((v n)^(1/r) : ℝ) : ℂ) = 0
    rw [hv, Real.zero_rpow (by positivity : 1/r ≠ 0)]
    simp

end NLS
