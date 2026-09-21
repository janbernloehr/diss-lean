import NLS.ZakharovShabat.RealGapCharacterization
import NLS.ComplexAnalysis.RealIntervalLevel

/-!
# The alternating discriminant inequality on each real gap
Continuity fixes the sign of the discriminant throughout a gap from its
known endpoint level. This gives the literal signed-index inequality
(-1)^n Delta >= 2 and the strict inequality in every open gap interior.
-/

noncomputable section
open Set Complex
open NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The discriminant keeps its endpoint parity level throughout each closed real gap. -/
theorem discriminant_parity_level_ge_two_on_canonicalGap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ) (x : ℝ)
    (hx : x ∈ Icc (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re) :
    2 ≤ if n % 2 = 0 then (canonicalDiscriminant hp φ x).re else -(canonicalDiscriminant hp φ x).re := by
  let f : ℝ → ℝ := fun y => if n % 2 = 0 then (canonicalDiscriminant hp φ y).re else -(canonicalDiscriminant hp φ y).re
  have hd : Continuous (canonicalDiscriminant hp φ) :=
    continuousOn_univ.mp (analyticOnNhd_canonicalDiscriminant hp hp1 φ heven).continuousOn
  have hcont : Continuous (fun y : ℝ => (canonicalDiscriminant hp φ (y : ℂ)).re) :=
    continuous_re.comp (hd.comp continuous_ofReal)
  have hf : Continuous f := by
    by_cases hn : n % 2 = 0
    · simp only [f,if_pos hn]; exact hcont
    · simp only [f,if_neg hn]; exact hcont.neg
  have hl : ((canonicalPeriodicLeft hp hp1 φ heven n).re : ℂ) = canonicalPeriodicLeft hp hp1 φ heven n := by
    apply Complex.ext
    · simp
    · simpa using (canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 φ heven hreal n).1.symm
  have hfa : f (canonicalPeriodicLeft hp hp1 φ heven n).re = 2 := by
    dsimp [f]
    rw [hl,(canonicalPeriodicEndpoints_discriminant_of_realType hp hp1 φ heven hreal n).1]
    split_ifs <;> norm_num
  apply level_le_on_Icc_of_sq_ge f (by norm_num : (0 : ℝ) < 2) hf.continuousOn hfa.ge _ x hx
  intro y hy
  have hs := discriminant_re_sq_ge_four_of_mem_canonicalGap hp hp1 φ heven hreal n y hy
  by_cases hn : n % 2 = 0 <;> simpa [f,hn,show (2 : ℝ)^2 = 4 by norm_num] using hs

/-- The source's alternating gap inequality, with integer powers at all signed indices. -/
theorem signed_discriminant_ge_two_on_canonicalGap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ) (x : ℝ)
    (hx : x ∈ Icc (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re) :
    2 ≤ (-1 : ℝ)^n*(canonicalDiscriminant hp φ x).re := by
  have h := discriminant_parity_level_ge_two_on_canonicalGap hp hp1 φ heven hreal n x hx
  rw [neg_one_zpow_eq_ite]
  by_cases hn : n % 2 = 0 <;> simpa [Int.even_iff,hn] using h

/-- In the interior of an open real gap the alternating inequality is strict. -/
theorem signed_discriminant_gt_two_on_canonicalGap_interior (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) (n : ℤ) (x : ℝ)
    (hx : x ∈ Ioo (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re) :
    2 < (-1 : ℝ)^n*(canonicalDiscriminant hp φ x).re := by
  have hge := discriminant_parity_level_ge_two_on_canonicalGap hp hp1 φ heven hreal n x ⟨hx.1.le,hx.2.le⟩
  have hgt := two_lt_norm_discriminant_of_mem_canonicalGap_interior hp hp1 φ heven hreal n x hx
  have hs := norm_canonicalDiscriminant_sq_of_realType hp hp1 φ heven hreal x
  rw [neg_one_zpow_eq_ite]
  by_cases hn : n % 2 = 0
  · simp only [if_pos hn] at hge
    simp only [Int.even_iff,hn,if_true,one_mul]
    nlinarith
  · simp only [if_neg hn] at hge
    simp only [Int.even_iff,hn,if_false,neg_one_mul]
    nlinarith

/-- The literal closed-gap union equals the real superlevel set of the discriminant modulus. -/
theorem real_discriminant_superlevel_eq_canonicalGaps (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : PairSpace p) (heven : φ ∈ pairParitySubspace 0) (hreal : IsRealType φ) :
    {x : ℝ | 2 ≤ ‖canonicalDiscriminant hp φ x‖} =
      ⋃ n : ℤ, Icc (canonicalPeriodicLeft hp hp1 φ heven n).re (canonicalPeriodicRight hp hp1 φ heven n).re := by
  ext x
  simpa only [mem_ofPred_eq,mem_iUnion] using two_le_norm_discriminant_iff_mem_canonicalGap hp hp1 φ heven hreal x

end NLS.ZakharovShabat
