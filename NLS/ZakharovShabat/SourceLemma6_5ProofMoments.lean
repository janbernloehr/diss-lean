import NLS.ZakharovShabat.SourceLemma6_5ProofExpansion
import NLS.SequenceSpaces.ReciprocalTail
import NLS.SequenceSpaces.SpectralReflectionTail

/-! # The selected reciprocal moments in the proof of Lemma 6.5

The exact far set is bounded by two one-factor reciprocal tails. The near
moment has the full lattice bound. One explicit positive exponent-only
constant supplies both printed subsum estimates and their 2^(1/p)
recombination, including p=1, the zero strip and both physical components.
-/

noncomputable section
open scoped ENNReal
open Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every selected reciprocal moment is bounded by the squared conjugate lattice constant. -/
theorem sourceLemma65Moment_selected_le (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (S : Set (ℤ × ℤ)) :
    (∑' kl, if kl ∈ S then (sourceLemma65ProofReciprocal n kl)^p.conjExponent.toReal else 0)^(1/p.conjExponent.toReal) ≤
      (Coeff.complementaryConstant p hp)^2 := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  have hq1 := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  have hq : p.conjExponent ≠ ⊤ := ne_of_lt
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1)
  have hqpos : 0 < p.conjExponent.toReal := ENNReal.toReal_pos (by positivity) hq
  let a := Coeff.shift n (Coeff.puncturedLattice p.conjExponent hq1)
  have he (kl : ℤ × ℤ) : sourceLemma65ProofReciprocal n kl = ‖a kl.1‖*‖a kl.2‖ := by
    rw [Coeff.norm_shift_puncturedLattice_apply,Coeff.norm_shift_puncturedLattice_apply]
    by_cases hk : kl.1 = n <;> by_cases hl : kl.2 = n <;>
      simp [sourceLemma65ProofReciprocal,hk,hl,abs_sub_comm,mul_comm]
  have ha := (lp.memℓp a).summable hqpos
  have hap := ha.mul_of_nonneg ha (fun _ => by positivity) (fun _ => by positivity)
  have hfull : (∑' kl, (sourceLemma65ProofReciprocal n kl)^p.conjExponent.toReal) =
      ‖a‖^p.conjExponent.toReal * ‖a‖^p.conjExponent.toReal := by
    simp only [he,Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    rw [← ha.tsum_mul_tsum ha hap,← lp.norm_rpow_eq_tsum hqpos]
  have hs := sourceLemma65ProofReciprocal_moment hp hp1 n
  have hn (kl) : 0 ≤ (sourceLemma65ProofReciprocal n kl)^p.conjExponent.toReal := by
    unfold sourceLemma65ProofReciprocal; positivity
  have hle (kl) : (if kl ∈ S then (sourceLemma65ProofReciprocal n kl)^p.conjExponent.toReal else 0) ≤
      (sourceLemma65ProofReciprocal n kl)^p.conjExponent.toReal := by split_ifs; exact le_rfl; exact hn kl
  have hm := hs.of_nonneg_of_le (fun kl => by split_ifs; exact hn kl; exact le_rfl) hle
  have h := Real.rpow_le_rpow (tsum_nonneg (fun kl => by split_ifs; exact hn kl; exact le_rfl))
    (hm.tsum_le_tsum hle hs) (by positivity : 0 ≤ 1/p.conjExponent.toReal)
  rw [hfull,← Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
    ← Real.rpow_mul (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
    mul_one_div_cancel hqpos.ne',Real.rpow_one] at h
  apply h.trans
  rw [pow_two]
  have haC : ‖a‖ ≤ Coeff.complementaryConstant p hp := by
    simpa only [a,Coeff.norm_shift] using Coeff.norm_puncturedLattice_le_complementaryConstant p hp
  exact mul_le_mul haC haC (norm_nonneg _) (Coeff.complementaryConstant_nonneg p hp)

end NLS.ZakharovShabat

namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
local instance sourceLemma65MomentFactConj : Fact (1 ≤ p.conjExponent) :=
  ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩

/-- The far reciprocal moment is bounded by the two one-factor lattice tails. -/
theorem sourceLemma65Moment_far_le (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    let hq1 := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
    let a := Coeff.shift n (Coeff.puncturedLattice p.conjExponent hq1)
    (∑' kl, if sourceLemma65ProofFar n kl.1 kl.2 then
      (sourceLemma65ProofReciprocal n kl)^p.conjExponent.toReal else 0)^(1/p.conjExponent.toReal) ≤
      2 * ‖a‖ * ‖a - Coeff.truncate (resonantWindow n) a‖ := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  let hq1 := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  let a := Coeff.shift n (Coeff.puncturedLattice p.conjExponent hq1)
  let b := a - Coeff.truncate (resonantWindow n) a
  have hq : p.conjExponent ≠ ⊤ := ne_of_lt
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1)
  have hqpos : 0 < p.conjExponent.toReal := ENNReal.toReal_pos (by positivity) hq
  have hqreal : 1 ≤ p.conjExponent.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hq (show 1 ≤ p.conjExponent from Fact.out)
  have he (kl : ℤ × ℤ) : sourceLemma65ProofReciprocal n kl = ‖a kl.1‖ * ‖a kl.2‖ := by
    rw [Coeff.norm_shift_puncturedLattice_apply,Coeff.norm_shift_puncturedLattice_apply]
    by_cases hk : kl.1 = n <;> by_cases hl : kl.2 = n <;>
      simp [sourceLemma65ProofReciprocal,hk,hl,abs_sub_comm,mul_comm]
  have hb (k : ℤ) (hk : k ∉ resonantWindow n) : b k = a k := by
    simp [b,hk]
  have hle (kl : ℤ × ℤ) :
      (if sourceLemma65ProofFar n kl.1 kl.2 then (sourceLemma65ProofReciprocal n kl)^p.conjExponent.toReal else 0) ≤
        ‖b kl.1‖^p.conjExponent.toReal * ‖a kl.2‖^p.conjExponent.toReal +
        ‖a kl.1‖^p.conjExponent.toReal * ‖b kl.2‖^p.conjExponent.toReal := by
    split_ifs with hfar
    · rw [he,Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
      rcases hfar.2.2 with hk | hl
      · have hk' : kl.1 ∉ resonantWindow n := by
          rw [← sourceLemma65Proof_half_radius_iff]; exact not_le.mpr hk
        rw [hb kl.1 hk']
        exact le_add_of_nonneg_right (by positivity)
      · have hl' : kl.2 ∉ resonantWindow n := by
          rw [← sourceLemma65Proof_half_radius_iff]; exact not_le.mpr hl
        rw [hb kl.2 hl']
        exact le_add_of_nonneg_left (by positivity)
    · positivity
  have ha := (lp.memℓp a).summable hqpos
  have hbs := (lp.memℓp b).summable hqpos
  have hba := hbs.mul_of_nonneg ha (fun _ => by positivity) (fun _ => by positivity)
  have hab := ha.mul_of_nonneg hbs (fun _ => by positivity) (fun _ => by positivity)
  have hm := (hba.add hab).of_nonneg_of_le (fun kl => by
    split_ifs
    · unfold sourceLemma65ProofReciprocal; positivity
    · exact le_rfl) hle
  have hsum := hm.tsum_le_tsum hle (hba.add hab)
  rw [hba.tsum_add hab,← hbs.tsum_mul_tsum ha hba,← ha.tsum_mul_tsum hbs hab,
    ← lp.norm_rpow_eq_tsum hqpos,← lp.norm_rpow_eq_tsum hqpos] at hsum
  have hsum' : (∑' kl, if sourceLemma65ProofFar n kl.1 kl.2 then
      (sourceLemma65ProofReciprocal n kl)^p.conjExponent.toReal else 0) ≤
        2 * (‖a‖*‖b‖)^p.conjExponent.toReal := by
    rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    nlinarith only [hsum]
  have h := Real.rpow_le_rpow (tsum_nonneg (fun kl => by
      split_ifs
      · unfold sourceLemma65ProofReciprocal; positivity
      · exact le_rfl)) hsum' (by positivity : 0 ≤ 1/p.conjExponent.toReal)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Real.rpow_nonneg (by positivity) _),
    ← Real.rpow_mul (mul_nonneg (norm_nonneg _) (norm_nonneg _)),
    mul_one_div_cancel hqpos.ne',Real.rpow_one] at h
  have htwo : (2:ℝ)^(1/p.conjExponent.toReal) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      ((div_le_one hqpos).mpr hqreal)
  exact h.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right htwo (mul_nonneg (norm_nonneg a) (norm_nonneg b)))

/-- The centered punctured lattice has the explicit reciprocal window-tail decay. -/
theorem sourceLemma65Moment_lattice_tail (hp : p ≠ ⊤) {n : ℤ} (hn : n ≠ 0) :
    let hq1 := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
    let a := Coeff.shift n (Coeff.puncturedLattice p.conjExponent hq1)
    ‖a - Coeff.truncate (resonantWindow n) a‖ ≤
      (16*p.toReal)*(n.natAbs:ℝ)^(-(1/p.toReal)) := by
  let hq1 := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  let a := Coeff.shift n (Coeff.puncturedLattice p.conjExponent hq1)
  have hN : 0 < n.natAbs := by omega
  have h := Coeff.norm_centered_reciprocal_windowTail_le_simple hp n.natAbs hN n
    (r := 1/2) (by norm_num) a (fun k => ?_)
  · convert h using 1
    · rfl
    · ring
  · rw [Coeff.norm_shift_puncturedLattice_apply]
    by_cases hk : k = n
    · simp [hk]
    · rw [if_neg hk]
      have ha : 1 ≤ |((k-n:ℤ):ℝ)| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr hk)
      rw [← div_eq_mul_inv,inv_eq_one_div]
      apply (div_le_div_iff₀ (by linarith) (by positivity)).mpr
      linarith

/-- Direct far reciprocal-moment decay, before introducing the inhomogeneous bracket. -/
theorem sourceLemma65Moment_far_decay (hp : p ≠ ⊤) (hp1 : 1 < p) {n : ℤ} (hn : n ≠ 0) :
    (∑' kl, if sourceLemma65ProofFar n kl.1 kl.2 then
      (sourceLemma65ProofReciprocal n kl)^p.conjExponent.toReal else 0)^(1/p.conjExponent.toReal) ≤
      (32*p.toReal*Coeff.complementaryConstant p hp)*(n.natAbs:ℝ)^(-(1/p.toReal)) := by
  have h := sourceLemma65Moment_far_le hp hp1 n
  dsimp only at h
  apply h.trans
  have hC := Coeff.complementaryConstant_nonneg p hp
  have ha := Coeff.norm_puncturedLattice_le_complementaryConstant p hp
  have ht := sourceLemma65Moment_lattice_tail hp hn
  dsimp only at ht
  rw [Coeff.norm_shift]
  calc
    _ ≤ 2 * Coeff.complementaryConstant p hp *
        ((16*p.toReal)*(n.natAbs:ℝ)^(-(1/p.toReal))) := by gcongr
    _ = _ := by ring

end NLS.ZakharovShabat

namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The reciprocal lattice constant is at least two, so the double-inverse budget is at least four. -/
theorem sourceLemma65Moment_budget_four (hp : p ≠ ⊤) : 4 ≤ weightedDoubleConstant (p := p) hp := by
  have hC : 2 ≤ Coeff.complementaryConstant p hp := le_max_right _ _
  have hp0 := ENNReal.toReal_nonneg (a := p)
  have hprod : 0 ≤ 64*p.toReal*Coeff.complementaryConstant p hp := by positivity
  unfold weightedDoubleConstant
  nlinarith only [hC,hprod]

/-- A nonzero integer radius controls the exact half-radius bracket used on p.38. -/
theorem sourceLemma65Moment_half_bracket (hp : p ≠ ⊤) {N : ℕ} (hN : 0 < N) :
    (N:ℝ)^(-(1/p.toReal)) ≤ 2*(1+(N:ℝ)/2)^(-(1/p.toReal)) := by
  have hp1 : 1 ≤ p.toReal := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  have hN1 : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  calc
    _ ≤ ((1+(N:ℝ)/2)/2)^(-(1/p.toReal)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (neg_nonpos.mpr (by positivity))
    _ ≤ _ := Coeff.half_radius_rpow_le hp1 (by positivity)

/-- The selected far reciprocal moment obeys the printed half-bracket decay at every index. -/
theorem sourceLemma65Moment_far_bracket (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    (∑' kl, if sourceLemma65ProofFar n kl.1 kl.2 then
      (sourceLemma65ProofReciprocal n kl)^p.conjExponent.toReal else 0)^(1/p.conjExponent.toReal) ≤
      weightedDoubleConstant (p := p) hp * (1+|(n:ℝ)|/2)^(-(1/p.toReal)) := by
  have hC := Coeff.complementaryConstant_nonneg p hp
  have hD : Coeff.complementaryConstant p hp ^ 2 ≤ weightedDoubleConstant (p := p) hp := by
    unfold weightedDoubleConstant
    exact le_add_of_nonneg_left (by positivity)
  by_cases hn : n = 0
  · subst n
    simpa using (sourceLemma65Moment_selected_le hp hp1 0 {kl | sourceLemma65ProofFar 0 kl.1 kl.2}).trans hD
  · have hN := sourceLemma65Moment_half_bracket hp (show 0 < n.natAbs by omega)
    have habs : (n.natAbs:ℝ) = |(n:ℝ)| := by simp
    rw [habs] at hN
    have h := sourceLemma65Moment_far_decay hp hp1 hn
    rw [habs] at h
    have hbudget : 64*p.toReal*Coeff.complementaryConstant p hp ≤ weightedDoubleConstant (p := p) hp :=
      le_add_of_nonneg_right (sq_nonneg _)
    calc
      _ ≤ (32*p.toReal*Coeff.complementaryConstant p hp)*|(n:ℝ)|^(-(1/p.toReal)) := h
      _ ≤ (64*p.toReal*Coeff.complementaryConstant p hp)*(1+|(n:ℝ)|/2)^(-(1/p.toReal)) := by
        have hh := mul_le_mul_of_nonneg_left hN (show 0 ≤ 32*p.toReal*Coeff.complementaryConstant p hp by positivity)
        convert hh using 1 <;> first | rfl | ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg (by positivity) _)

/-- The selected near sum has the exact remainder and inverse weight with one exponent-only budget. -/
theorem sourceLemma65Moment_near (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ f : WeightedCoeff w.toWeight p) (n : ℤ) :
    (∑' kl, if sourceLemma65ProofNear n kl.1 kl.2 then sourceLemma65ProofTerm w φ f n kl else 0) ≤
      (weightedDoubleConstant (p := p) hp / w n) *
        (‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ‖*w.shiftedNorm (-n) f) := by
  apply (sourceLemma65Proof_near_holder_tail hp hp1 w φ f n).trans
  have hm := sourceLemma65Moment_selected_le hp hp1 n {kl | sourceLemma65ProofNear n kl.1 kl.2}
  have hC := Coeff.complementaryConstant_nonneg p hp
  have hD : Coeff.complementaryConstant p hp ^ 2 ≤ weightedDoubleConstant (p := p) hp := by
    unfold weightedDoubleConstant
    exact le_add_of_nonneg_left (by positivity)
  have hw := w.positive n
  have hf : 0 ≤ w.shiftedNorm (-n) f := norm_nonneg _
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hm.trans hD) (by positivity : 0 ≤ 1/w n))
    (mul_nonneg (norm_nonneg (WeightedCoeff.fourierTail w.toWeight n.natAbs φ)) hf)
  simpa only [div_eq_mul_inv,one_mul,mul_comm,mul_left_comm,mul_assoc,Set.mem_ofPred_eq] using h

/-- The far sum retains the source half-bracket and original scalar norms. -/
theorem sourceLemma65Moment_far (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ f : WeightedCoeff w.toWeight p) (n : ℤ) :
    (∑' kl, if sourceLemma65ProofFar n kl.1 kl.2 then sourceLemma65ProofTerm w φ f n kl else 0) ≤
      (weightedDoubleConstant (p := p) hp * (1+|(n:ℝ)|/2)^(-(1/p.toReal))) *
        (‖φ‖*w.shiftedNorm (-n) f) := by
  exact (sourceLemma65Proof_far_holder_norm hp hp1 w φ f n).trans
    (mul_le_mul_of_nonneg_right (sourceLemma65Moment_far_bracket hp hp1 n)
      (mul_nonneg (norm_nonneg _) (show 0 ≤ w.shiftedNorm (-n) f from norm_nonneg _)))

end NLS.ZakharovShabat

namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The printed near estimate holds at every finite Banach exponent, including p=1. -/
theorem sourceLemma65Moment_near_all (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeff w.toWeight p) (n : ℤ) :
    (∑' kl, if sourceLemma65ProofNear n kl.1 kl.2 then sourceLemma65ProofTerm w φ f n kl else 0) ≤
      (weightedDoubleConstant (p := p) hp / w n) *
        (‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ‖*w.shiftedNorm (-n) f) := by
  by_cases hp1 : p = 1
  · subst p
    apply (sourceLemma65Proof_near_one w φ f n).trans
    have hD : 1 ≤ weightedDoubleConstant (p := 1) hp := (by norm_num : (1:ℝ) ≤ 4).trans (sourceLemma65Moment_budget_four hp)
    apply mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hD (w.positive n).le)
    exact mul_nonneg (norm_nonneg _) (show 0 ≤ w.shiftedNorm (-n) f from norm_nonneg _)
  · exact sourceLemma65Moment_near hp (lt_of_le_of_ne Fact.out (Ne.symm hp1)) w φ f n

/-- The printed far estimate includes the conjugate-infinity endpoint and zero strip. -/
theorem sourceLemma65Moment_far_all (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeff w.toWeight p) (n : ℤ) :
    (∑' kl, if sourceLemma65ProofFar n kl.1 kl.2 then sourceLemma65ProofTerm w φ f n kl else 0) ≤
      (weightedDoubleConstant (p := p) hp * (1+|(n:ℝ)|/2)^(-(1/p.toReal))) *
        (‖φ‖*w.shiftedNorm (-n) f) := by
  by_cases hp1 : p = 1
  · subst p
    have hD : 2 ≤ weightedDoubleConstant (p := 1) hp := (by norm_num : (2:ℝ) ≤ 4).trans (sourceLemma65Moment_budget_four hp)
    have hb : 2/(1+|(n:ℝ)|) ≤ weightedDoubleConstant (p := 1) hp/(1+|(n:ℝ)|/2) := by
      calc
        _ ≤ 2/(1+|(n:ℝ)|/2) := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith [abs_nonneg (n:ℝ)])
        _ ≤ _ := div_le_div_of_nonneg_right hD (by positivity)
    have h := (sourceLemma65Proof_far_one w φ f n).trans
      (mul_le_mul_of_nonneg_right hb (mul_nonneg (norm_nonneg _) (show 0 ≤ w.shiftedNorm (-n) f from norm_nonneg _)))
    simpa only [ENNReal.toReal_one,div_one,Real.rpow_neg_one,div_eq_mul_inv,inv_one,mul_one] using h
  · exact sourceLemma65Moment_far hp (lt_of_le_of_ne Fact.out (Ne.symm hp1)) w φ f n

omit [Fact (1 ≤ p)] in
/-- The half-bracket to full-bracket conversion has exactly the printed factor 2^(1/p). -/
theorem sourceLemma65Moment_half_to_full (n : ℤ) :
    (1+|(n:ℝ)|/2)^(-(1/p.toReal)) ≤
      (2:ℝ)^(1/p.toReal)*(1+|(n:ℝ)|)^(-(1/p.toReal)) := by
  calc
    _ ≤ ((1+|(n:ℝ)|)/2)^(-(1/p.toReal)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (neg_nonpos.mpr (by positivity))
    _ = _ := by
      rw [Real.div_rpow (by positivity) (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_inv_eq_mul,mul_comm]

/-- Recombining the literal subsums gives the exact printed 2^(1/p) form. -/
theorem sourceLemma65Moment_recombine (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeff w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    w.shiftedNorm (-n) (complementarySandwich hp w φ n z hz false f) ≤
      (2:ℝ)^(1/p.toReal) * weightedDoubleConstant (p := p) hp *
        (‖φ‖/(1+|(n:ℝ)|)^(1/p.toReal) + ‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ‖/w n) *
        w.shiftedNorm (-n) f := by
  have hsum := sourceLemma65Proof_norm_le_literal hp w φ f n z hz
  rw [sourceLemma65ProofTerm_split hp] at hsum
  have h := hsum.trans (add_le_add (sourceLemma65Moment_far_all hp w φ f n) (sourceLemma65Moment_near_all hp w φ f n))
  have hD := weightedDoubleConstant_nonneg (p := p) hp
  have hf : 0 ≤ w.shiftedNorm (-n) f := norm_nonneg _
  have hw := w.positive n
  have ht : 0 ≤ ‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ‖/w n := by positivity
  have htwo : 1 ≤ (2:ℝ)^(1/p.toReal) := Real.one_le_rpow (by norm_num) (by positivity)
  have hfar := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sourceLemma65Moment_half_to_full (p := p) n) hD)
    (mul_nonneg (norm_nonneg φ) hf)
  have hnear := mul_le_mul_of_nonneg_right htwo (mul_nonneg (mul_nonneg hD ht) hf)
  have hadd := add_le_add hfar hnear
  apply h.trans
  rw [Real.rpow_neg (by positivity : 0 ≤ 1+|(n:ℝ)|)] at hadd
  convert hadd using 1 <;> ring

/-- One explicit exponent-only choice realizes every occurrence of c_p squared in this proof. -/
def sourceLemma65ProofConstant (hp : p ≠ ⊤) : ℝ := Real.sqrt (weightedDoubleConstant (p := p) hp)

theorem sourceLemma65ProofConstant_sq (hp : p ≠ ⊤) :
    sourceLemma65ProofConstant hp ^ 2 = weightedDoubleConstant (p := p) hp :=
  Real.sq_sqrt (weightedDoubleConstant_nonneg hp)

theorem sourceLemma65ProofConstant_pos (hp : p ≠ ⊤) : 0 < sourceLemma65ProofConstant hp :=
  Real.sqrt_pos.mpr ((by norm_num : (0:ℝ) < 4).trans_le (sourceLemma65Moment_budget_four hp))

/-- The other physical component has the same printed estimate with the opposite shift. -/
theorem sourceLemma65Moment_recombine_true (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeff w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    w.shiftedNorm n (complementarySandwich hp w φ n z hz true f) ≤
      (2:ℝ)^(1/p.toReal) * weightedDoubleConstant (p := p) hp *
        (‖φ‖/(1+|(n:ℝ)|)^(1/p.toReal) + ‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ‖/w n) *
        w.shiftedNorm n f := by
  rw [sourceLemma65Proof_true_reflection,SpectralWeight.shiftedNorm_reflection]
  simpa only [LinearIsometryEquiv.norm_map,SpectralWeight.norm_fourierTail_reflection,
    SpectralWeight.shiftedNorm_reflection,neg_neg] using
    sourceLemma65Moment_recombine hp w (w.reflection φ) (w.reflection f) n z hz

end NLS.ZakharovShabat

namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both literal component estimates use one positive exponent-only c_p and the original shifts. -/
theorem sourceLemma65Moment_original_bounds (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    w.shiftedNorm n (sourceLemma65Vector_original hp w φ f n z hz).fst ≤
      (2:ℝ)^(1/p.toReal) * sourceLemma65ProofConstant hp ^ 2 *
        (‖φ.fst‖/(1+|(n:ℝ)|)^(1/p.toReal) + ‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ.fst‖/w n) *
        w.shiftedNorm n f.snd ∧
    w.shiftedNorm (-n) (sourceLemma65Vector_original hp w φ f n z hz).snd ≤
      (2:ℝ)^(1/p.toReal) * sourceLemma65ProofConstant hp ^ 2 *
        (‖φ.snd‖/(1+|(n:ℝ)|)^(1/p.toReal) + ‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ.snd‖/w n) *
        w.shiftedNorm (-n) f.fst := by
  rw [sourceLemma65ProofConstant_sq,(sourceLemma65Vector_original_components hp w φ f n z hz).1,
    (sourceLemma65Vector_original_components hp w φ f n z hz).2]
  exact ⟨sourceLemma65Moment_recombine_true hp w φ.fst f.snd n z hz,
    sourceLemma65Moment_recombine hp w φ.snd f.fst n z hz⟩

end NLS.ZakharovShabat

namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The printed p.39 budget is an upper bound with the same explicit proof constant. -/
theorem sourceLemma65Proof_young_budget (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    sourceLemma65YoungMajorant hp w φ n z hz f ≤
      sourceLemma65PrintedProofBudget (sourceLemma65ProofConstant hp) w φ n f := by
  have hD := weightedDoubleConstant_nonneg (p := p) hp
  have hC := (sourceLemma65ProofConstant_pos hp).le
  have hw := w.positive n
  have hf : 0 ≤ w.shiftedPairNorm n f := norm_nonneg _
  let B := ‖φ‖/(1+|(n:ℝ)|)^(1/p.toReal) + ‖weightedPairFourierTail w.toWeight n.natAbs φ‖/w n
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound : weightedSquareBound hp w φ n = ‖φ‖*weightedDoubleConstant (p := p) hp*B := by
    unfold weightedSquareBound B
    rw [Real.rpow_neg (by positivity : 0 ≤ 1+|(n:ℝ)|)]
    ring
  have hpower : (weightedDoubleConstant (p := p) hp)^p.toReal =
      (sourceLemma65ProofConstant hp)^(2*p.toReal) := by
    rw [← sourceLemma65ProofConstant_sq hp,← Real.rpow_natCast,← Real.rpow_mul hC]
    norm_num
  apply (sourceLemma65YoungMajorant_le hp w φ n z hz f).trans
  rw [hbound,Real.mul_rpow (mul_nonneg (norm_nonneg _) hD) hB,
    Real.mul_rpow (norm_nonneg _) hD,hpower]
  change _ ≤ 2*(sourceLemma65ProofConstant hp)^(2*p.toReal)*‖φ‖^p.toReal*B^p.toReal*
    w.shiftedPairNorm n f ^p.toReal
  have hn : 0 ≤ (sourceLemma65ProofConstant hp)^(2*p.toReal)*‖φ‖^p.toReal*B^p.toReal*
      w.shiftedPairNorm n f ^p.toReal := by positivity
  nlinarith only [hn]

/-- The complete corrected last display is a chain of inequalities in the original norm. -/
theorem sourceLemma65Proof_corrected_chain (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    w.shiftedPairNorm n (weightedPotentialInverse hp w φ n z hz
      (weightedPotentialInverse hp w φ n z hz f))^p.toReal ≤
        sourceLemma65YoungMajorant hp w φ n z hz f ∧
    sourceLemma65YoungMajorant hp w φ n z hz f ≤
      sourceLemma65PrintedProofBudget (sourceLemma65ProofConstant hp) w φ n f :=
  ⟨sourceLemma65_square_le_young hp w φ n z hz f, sourceLemma65Proof_young_budget hp w φ f n z hz⟩

end NLS.ZakharovShabat
