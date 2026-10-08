import NLS.ZakharovShabat.AppendixDRelativeProductRows
import NLS.SequenceSpaces.UniformSelectionSup

/-! # Lemma D.6: suprema on the full source discs

Independent sampling gives the least majorant on every open quarter-pi
 disc. The powered suprema are summable, with an explicit uniform bound.
-/
noncomputable section
open Set Metric
open scoped ENNReal
open NLS.Fourier
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The least disc majorant belongs to the original coefficient space. -/
theorem exists_appendixDRelativeProductSup (hp1 : 1 < p) (hp : p ≠ ⊤)
    (r : Coeff ⊤) (a : Coeff p) {c B : ℝ} {N : ℕ}
    (hc : 0 < c) (hB : 0 ≤ B) (hr : ‖r‖ ≤ B)
    (hsep : AppendixDReferenceSeparated r c N) :
    ∃ b : Coeff p,
      (∀ n : ℤ, N ≤ n.natAbs → ∀ z ∈ refinedResonantDisk n,
        ‖appendixDRelativeProductError r a n z‖ ≤ ‖b n‖) ∧
      (∀ n : ℤ, N ≤ n.natAbs → ∀ t : ℝ, 0 ≤ t →
        (∀ z ∈ refinedResonantDisk n, ‖appendixDRelativeProductError r a n z‖ ≤ t) →
        ‖b n‖ ≤ t) ∧
      (∀ n : ℤ, ¬N ≤ n.natAbs → b n = 0) ∧
      ‖b‖ ≤ appendixDRelativeProductBound hp1 hp c B ‖a‖ := by
  have hD (n : ℤ) : (refinedResonantDisk n).Nonempty := by
    refine ⟨(Real.pi:ℂ)*n, ?_⟩
    simp only [refinedResonantDisk, mem_ball, dist_self]
    positivity
  have hK : 0 ≤ appendixDRelativeProductBound hp1 hp c B ‖a‖ := by
    have hH := hilbertTransformBound_nonneg hp1 hp
    unfold appendixDRelativeProductBound
    positivity
  exact NLS.exists_uniformSelectionSup hp {n : ℤ | N ≤ n.natAbs}
    refinedResonantDisk hD (appendixDRelativeProductError r a)
    (appendixDRelativeProductBound hp1 hp c B ‖a‖) hK
    (fun z hz => exists_appendixDRelativeProductRows hp1 hp r a hc hB hr hsep z
      (fun n _ => hz n))

/-- The literal powered disc supremum, extended by zero below the cutoff. -/
def appendixDRelativeProductPowerSup (r : Coeff ⊤) (a : Coeff p) (N : ℕ) (n : ℤ) : ℝ :=
  if N ≤ n.natAbs then
    sSup ((fun z => ‖appendixDRelativeProductError r a n z‖^p.toReal) '' refinedResonantDisk n)
  else 0

/-- Summability and the explicit power-sum estimate, with no additional tail smallness. -/
theorem appendixDRelativeProductPowerSup_bound (hp1 : 1 < p) (hp : p ≠ ⊤)
    (r : Coeff ⊤) (a : Coeff p) {c B : ℝ} {N : ℕ}
    (hc : 0 < c) (hB : 0 ≤ B) (hr : ‖r‖ ≤ B)
    (hsep : AppendixDReferenceSeparated r c N) :
    Summable (appendixDRelativeProductPowerSup r a N) ∧
      ∑' n : ℤ, appendixDRelativeProductPowerSup r a N n ≤
        (appendixDRelativeProductBound hp1 hp c B ‖a‖)^p.toReal := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  obtain ⟨b,hmajor,_,_,hb⟩ := exists_appendixDRelativeProductSup hp1 hp r a hc hB hr hsep
  have hpoint (n : ℤ) : 0 ≤ appendixDRelativeProductPowerSup r a N n ∧
      appendixDRelativeProductPowerSup r a N n ≤ ‖b n‖^p.toReal := by
    by_cases hn : N ≤ n.natAbs
    · let U := (fun z => ‖appendixDRelativeProductError r a n z‖^p.toReal) '' refinedResonantDisk n
      have hcenter : (Real.pi:ℂ)*n ∈ refinedResonantDisk n := by
        simp only [refinedResonantDisk, mem_ball, dist_self]
        positivity
      have hne : U.Nonempty := ⟨_, ⟨_,hcenter,rfl⟩⟩
      have hupper : ∀ u ∈ U, u ≤ ‖b n‖^p.toReal := by
        rintro u ⟨z,hz,rfl⟩
        exact Real.rpow_le_rpow (norm_nonneg _) (hmajor n hn z hz) hp0.le
      have hbounded : BddAbove U := ⟨_,hupper⟩
      change 0 ≤ (if N ≤ n.natAbs then sSup U else 0) ∧ _
      rw [if_pos hn]
      constructor
      · exact (Real.rpow_nonneg (norm_nonneg _) _).trans
          (le_csSup hbounded (show ‖appendixDRelativeProductError r a n ((Real.pi:ℂ)*n)‖^p.toReal ∈ U
            from ⟨_,hcenter,rfl⟩))
      · simpa only [appendixDRelativeProductPowerSup, if_pos hn] using csSup_le hne hupper
    · simp only [appendixDRelativeProductPowerSup, if_neg hn]
      exact ⟨le_rfl,Real.rpow_nonneg (norm_nonneg _) _⟩
  have hs := (lp.memℓp b).summable hp0
  have hsum := hs.of_nonneg_of_le (fun n => (hpoint n).1) (fun n => (hpoint n).2)
  refine ⟨hsum, (hsum.tsum_le_tsum (fun n => (hpoint n).2) hs).trans ?_⟩
  rw [← lp.norm_rpow_eq_tsum hp0]
  exact Real.rpow_le_rpow (norm_nonneg _) hb hp0.le

end NLS.ZakharovShabat
