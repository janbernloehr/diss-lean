import NLS.ZakharovShabat.SourceLemma6_5ProofDisplay
import NLS.SequenceSpaces.WeightedSandwichAbsoluteSum
import NLS.ZakharovShabat.SourceLemma34Holder
import NLS.SequenceSpaces.CompactPuncturedKernel

/-! # The literal series and Holder steps in the proof of Lemma 6.5

Both original components have the printed distance-denominator majorants.
The jointly convergent sum splits over the exact strict-far and closed-near
regions. Holder retains the selected reciprocal moments, original scalar
norms, signed shifts, and boundary-inclusive Fourier tail. The p=1 endpoint
also has explicit far decay and a recombined norm estimate.

The scalar reciprocal-moment simplifications for p>1 are a separate source
comparison; the existing operator norm estimate remains available.
-/

noncomputable section
open scoped ENNReal
open Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Literal signed raw components of the original double-inverse vector on p.38. -/
theorem sourceLemma65Proof_original_coefficients (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (k : ℤ) :
    let t := weightedPotentialInverse hp w φ n z hz f
    let g := sourceWeightedDomainInput w (complementaryFreeDomainInverse w.toWeight n z hz t)
    g.fst.val (-k) = ∑' l : ℤ, complementarySymbol n z k * complementarySymbol n z l *
      φ.fst.val (-(k+l)) * f.snd.val l ∧
    g.snd.val k = ∑' l : ℤ, complementarySymbol n z k * complementarySymbol n z l *
      φ.snd.val (k+l) * f.fst.val (-l) := by
  dsimp only
  constructor
  · simp only [sourceWeightedDomainInput_fst,complementaryFreeDomainInverse_fst,
      neg_neg,weightedPotentialInverse_fst,SpectralWeight.convolution_apply,
      complementaryScalarL1_apply,freeFrequency_false]
    rw [← tsum_mul_left]
    apply tsum_congr
    intro l
    rw [show -k-l = -(k+l) by ring]
    ring
  · simp only [sourceWeightedDomainInput_snd,complementaryFreeDomainInverse_snd,
      weightedPotentialInverse_snd,SpectralWeight.convolution_apply,
      complementaryScalarL1_apply,freeFrequency_true]
    rw [← tsum_mul_left]
    rw [← (Equiv.neg ℤ).tsum_eq]
    apply tsum_congr
    intro l
    simp only [Equiv.neg_apply,neg_neg,sub_neg_eq_add]
    ring

/-- The original exclusions and both literal denominators, including at the free center. -/
theorem sourceLemma65Proof_original_restricted (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) (k : ℤ) :
    let t := weightedPotentialInverse hp w φ n z hz f
    let g := sourceWeightedDomainInput w (complementaryFreeDomainInverse w.toWeight n z hz t)
    g.fst.val (-k) = (∑' l : ℤ, if k = n ∨ l = n then 0 else
      φ.fst.val (-(k+l))*f.snd.val l / ((z-(Real.pi:ℂ)*k)*(z-(Real.pi:ℂ)*l))) ∧
    g.snd.val k = (∑' l : ℤ, if k = n ∨ l = n then 0 else
      φ.snd.val (k+l)*f.fst.val (-l) / ((z-(Real.pi:ℂ)*k)*(z-(Real.pi:ℂ)*l))) := by
  dsimp only
  rw [(sourceLemma65Proof_original_coefficients hp w φ f n z hz k).1,
    (sourceLemma65Proof_original_coefficients hp w φ f n z hz k).2]
  constructor <;> apply tsum_congr <;> intro l <;>
    by_cases hk : k = n <;> by_cases hl : l = n <;>
    simp [complementarySymbol,hk,hl,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]

end NLS.ZakharovShabat

namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The exact distance-denominator majorant on p.38, in physical scalar coordinates. -/
def sourceLemma65ProofTerm (w : SpectralWeight) (φ f : WeightedCoeff w.toWeight p)
    (n : ℤ) (kl : ℤ × ℤ) : ℝ :=
  if kl.1 = n ∨ kl.2 = n then 0 else
    w (kl.1-n)*‖φ.val (kl.1+kl.2)‖*‖f.val (-kl.2)‖ /
      (|((n-kl.1 : ℤ):ℝ)| * |((n-kl.2 : ℤ):ℝ)|)

/-- The majorant is a full absolutely convergent series, including p=1. -/
theorem sourceLemma65ProofTerm_summable (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeff w.toWeight p) (n : ℤ) : Summable (sourceLemma65ProofTerm w φ f n) := by
  let : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
  let hq := (ENNReal.HolderConjugate.lt_top_iff_one_lt p p.conjExponent).mp hp.lt_top
  let a := Coeff.shift n (Coeff.puncturedLattice p.conjExponent hq)
  let b := Coeff.reindex (Equiv.neg ℤ) a
  have hs := (SpectralWeight.sandwich_weighted_sum w (-n) a φ b f).1
  let e := Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
  apply (e.summable_iff.mpr hs).congr
  intro kl
  change w (kl.1 + -n)*‖a kl.1‖*‖φ.val (kl.1-(-kl.2))‖*‖a (-(-kl.2))‖*‖f.val (-kl.2)‖ = _
  simp only [neg_neg,sub_neg_eq_add,← sub_eq_add_neg]
  rw [Coeff.norm_shift_puncturedLattice_apply,Coeff.norm_shift_puncturedLattice_apply]
  by_cases hk : kl.1 = n <;> by_cases hl : kl.2 = n <;>
    simp [sourceLemma65ProofTerm,hk,hl,abs_sub_comm,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]

omit [Fact (1 ≤ p)] in
/-- Each signed original coefficient term is bounded by the exact printed distance term. -/
theorem sourceLemma65ProofTerm_pointwise (w : SpectralWeight) (φ f : WeightedCoeff w.toWeight p)
    {n : ℤ} {z : ℂ} (hz : z ∈ resonantStrip n) (k l : ℤ) :
    w (k-n)*‖complementarySymbol n z k * complementarySymbol n z l *
      φ.val (k+l)*f.val (-l)‖ ≤ sourceLemma65ProofTerm w φ f n (k,l) := by
  by_cases hk : k = n
  · simp [sourceLemma65ProofTerm,hk]
  by_cases hl : l = n
  · simp [sourceLemma65ProofTerm,hl]
  have hden (m : ℤ) (hm : m ≠ n) :
      ‖complementarySymbol n z m‖ ≤ |((n-m : ℤ):ℝ)|⁻¹ := by
    rw [complementarySymbol,if_neg hm,norm_inv]
    have ha : 0 < |((m-n : ℤ):ℝ)| := abs_pos.mpr (by exact_mod_cast sub_ne_zero.mpr hm)
    simpa only [Int.cast_sub,abs_sub_comm] using inv_anti₀ ha (resonantStrip_denominator_lower hz hm)
  simp only [sourceLemma65ProofTerm,hk,hl,or_self,if_false,norm_mul]
  have hw := w.positive (k-n)
  calc
    _ ≤ w (k-n)*(|((n-k : ℤ):ℝ)|⁻¹*|((n-l : ℤ):ℝ)|⁻¹*‖φ.val (k+l)‖*‖f.val (-l)‖) := by
      gcongr
      · exact hden k hk
      · exact hden l hl
    _ = _ := by simp only [div_eq_mul_inv,mul_inv]; ring

/-- The actual positive-oriented sandwich satisfies the literal p.38 l1 majorization. -/
theorem sourceLemma65Proof_norm_le_literal (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeff w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    w.shiftedNorm (-n) (complementarySandwich hp w φ n z hz false f) ≤
      ∑' kl : ℤ × ℤ, sourceLemma65ProofTerm w φ f n kl := by
  let g := complementarySandwich hp w φ n z hz false f
  let U (k l : ℤ) : ℂ := (w (k-n):ℂ)*complementarySymbol n z k*
    complementarySymbol n z l*φ.val (k+l)*f.val (-l)
  have hs := sourceLemma65ProofTerm_summable hp w φ f n
  have hU (k l : ℤ) : ‖U k l‖ ≤ sourceLemma65ProofTerm w φ f n (k,l) := by
    have h := sourceLemma65ProofTerm_pointwise w φ f hz k l
    simpa only [U,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (w.positive (k-n)),mul_assoc] using h
  have hc (k : ℤ) : (w (k-n):ℂ)*g.val k = ∑' l : ℤ, U k l := by
    simp only [g,complementarySandwich_apply,Bool.not_false,freeFrequency_false,freeFrequency_true]
    rw [← (Equiv.neg ℤ).tsum_eq]
    simp only [Equiv.neg_apply,neg_neg,sub_neg_eq_add]
    rw [← tsum_mul_left,← tsum_mul_left]
    apply tsum_congr
    intro l
    dsimp [U]
    ring
  have hrow (k : ℤ) : w (k-n)*‖g.val k‖ ≤ ∑' l : ℤ, sourceLemma65ProofTerm w φ f n (k,l) := by
    have hUs := (hs.prod_factor k).of_nonneg_of_le (fun _ => norm_nonneg _) (hU k)
    have h := (norm_tsum_le_tsum_norm hUs).trans (hUs.tsum_le_tsum (hU k) (hs.prod_factor k))
    rw [← hc] at h
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (w.positive (k-n))] using h
  have hgs : Summable (fun k : ℤ => w (k-n)*‖g.val k‖) := by
    simpa only [ENNReal.toReal_one,Real.rpow_one,← sub_eq_add_neg] using
      w.summable_shiftedNorm_terms (by simp : (1:ℝ≥0∞) ≠ ⊤) (-n) g
  calc
    _ = ∑' k : ℤ, w (k-n)*‖g.val k‖ := by
      simpa only [ENNReal.toReal_one,Real.rpow_one,← sub_eq_add_neg] using
        w.shiftedNorm_rpow_eq_tsum (by simp : (1:ℝ≥0∞) ≠ ⊤) (-n) g
    _ ≤ ∑' k : ℤ, ∑' l : ℤ, sourceLemma65ProofTerm w φ f n (k,l) := hgs.tsum_le_tsum hrow hs.prod
    _ = _ := hs.tsum_prod.symm

end NLS.ZakharovShabat

namespace NLS.ZakharovShabat

/-- The source near region, retaining both excluded resonant frequencies. -/
def sourceLemma65ProofNear (n k l : ℤ) : Prop :=
  k ≠ n ∧ l ≠ n ∧ |((n-k:ℤ):ℝ)| ≤ |(n:ℝ)|/2 ∧ |((n-l:ℤ):ℝ)| ≤ |(n:ℝ)|/2

/-- The source far region, with a strict half-radius inequality. -/
def sourceLemma65ProofFar (n k l : ℤ) : Prop :=
  k ≠ n ∧ l ≠ n ∧ (|(n:ℝ)|/2 < |((n-k:ℤ):ℝ)| ∨ |(n:ℝ)|/2 < |((n-l:ℤ):ℝ)|)

theorem sourceLemma65Proof_half_radius_iff (n k : ℤ) :
    |((n-k:ℤ):ℝ)| ≤ |(n:ℝ)|/2 ↔ k ∈ resonantWindow n := by
  have he : |((n-k:ℤ):ℝ)| = ((k-n).natAbs:ℝ) := by
    simp only [Nat.cast_natAbs,Int.cast_abs,Int.cast_sub,abs_sub_comm]
  rw [he,show |(n:ℝ)| = (n.natAbs:ℝ) by simp,mem_resonantWindow]
  constructor
  · intro h
    have hh : (2*(k-n).natAbs:ℕ) ≤ n.natAbs := by exact_mod_cast (show 2*((k-n).natAbs:ℝ) ≤ (n.natAbs:ℝ) by linarith)
    omega
  · intro h
    have hh : (2*(k-n).natAbs:ℕ) ≤ n.natAbs := by omega
    have hr : 2*((k-n).natAbs:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast hh
    linarith

/-- The literal near region is exactly the pair of opposite physical windows. -/
theorem sourceLemma65ProofNear_iff (n k l : ℤ) :
    sourceLemma65ProofNear n k l ↔ k ≠ n ∧ l ≠ n ∧ k ∈ resonantWindow n ∧ -l ∈ resonantWindow (-n) := by
  have hl : l ∈ resonantWindow n ↔ -l ∈ resonantWindow (-n) := by
    simp only [mem_resonantWindow,Int.natAbs_neg]
    rw [show -l- -n = -(l-n) by omega,Int.natAbs_neg]
  simp only [sourceLemma65ProofNear,sourceLemma65Proof_half_radius_iff,hl]

/-- The far region is the complement of near inside the admissible nonresonant pairs. -/
theorem sourceLemma65ProofFar_iff (n k l : ℤ) :
    sourceLemma65ProofFar n k l ↔ k ≠ n ∧ l ≠ n ∧ ¬ sourceLemma65ProofNear n k l := by
  simp only [sourceLemma65ProofFar,sourceLemma65ProofNear,not_and_or,not_not,not_le]
  tauto

/-- Exact source weight gain on the near region, with the physical input sign retained. -/
theorem sourceLemma65ProofNear_weight (w : SpectralWeight) {n k l : ℤ} (h : sourceLemma65ProofNear n k l) :
    w (k-n)*w n ≤ w (k+l)*w (-l-n) := by
  obtain ⟨_,_,hk,hl⟩ := (sourceLemma65ProofNear_iff n k l).mp h
  simpa only [sub_neg_eq_add] using resonantWindows_weight_gain w hk hl

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The near region sees precisely the boundary-inclusive potential remainder. -/
theorem sourceLemma65ProofNear_tail (w : SpectralWeight) (φ : WeightedCoeff w.toWeight p)
    {n k l : ℤ} (h : sourceLemma65ProofNear n k l) :
    (WeightedCoeff.fourierTail w.toWeight n.natAbs φ).val (k+l) = φ.val (k+l) := by
  obtain ⟨_,_,hk,hl⟩ := (sourceLemma65ProofNear_iff n k l).mp h
  have hn : n.natAbs ≤ (k+l).natAbs := by simpa only [sub_neg_eq_add] using resonantWindows_tail hk hl
  simp only [WeightedCoeff.fourierTail_apply,if_pos hn]

/-- Exact splitting of the jointly convergent printed majorant into the two source regions. -/
theorem sourceLemma65ProofTerm_split (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeff w.toWeight p) (n : ℤ) :
    (∑' kl : ℤ × ℤ, sourceLemma65ProofTerm w φ f n kl) =
      (∑' kl : ℤ × ℤ, if sourceLemma65ProofFar n kl.1 kl.2 then sourceLemma65ProofTerm w φ f n kl else 0) +
      (∑' kl : ℤ × ℤ, if sourceLemma65ProofNear n kl.1 kl.2 then sourceLemma65ProofTerm w φ f n kl else 0) := by
  have hs := sourceLemma65ProofTerm_summable hp w φ f n
  have hn (kl : ℤ × ℤ) : 0 ≤ sourceLemma65ProofTerm w φ f n kl := by
    dsimp [sourceLemma65ProofTerm]
    split_ifs
    · exact le_rfl
    · have hw := w.positive (kl.1-n); positivity
  have hm (P : ℤ × ℤ → Prop) [DecidablePred P] :
      Summable (fun kl => if P kl then sourceLemma65ProofTerm w φ f n kl else 0) := by
    exact hs.of_nonneg_of_le (fun kl => by split_ifs <;> first | exact hn kl | exact le_rfl)
      (fun kl => by split_ifs <;> simp only [le_refl,hn])
  rw [← (hm (fun kl => sourceLemma65ProofFar n kl.1 kl.2)).tsum_add (hm (fun kl => sourceLemma65ProofNear n kl.1 kl.2))]
  apply tsum_congr
  intro kl
  rw [sourceLemma65ProofFar_iff]
  by_cases hk : kl.1 = n <;> by_cases hl : kl.2 = n <;>
    by_cases hnear : sourceLemma65ProofNear n kl.1 kl.2 <;> simp [hk,hl,hnear,sourceLemma65ProofTerm]

end NLS.ZakharovShabat

namespace NLS.ZakharovShabat

/-- Reciprocal product, extended by zero at either excluded resonant index. -/
def sourceLemma65ProofReciprocal (n : ℤ) (kl : ℤ × ℤ) : ℝ :=
  (|((n-kl.1:ℤ):ℝ)| * |((n-kl.2:ℤ):ℝ)|)⁻¹

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source weighted numerator, with the reflected physical input and its exact shift. -/
def sourceLemma65ProofNumerator (w : SpectralWeight) (φ f : WeightedCoeff w.toWeight p)
    (n : ℤ) (kl : ℤ × ℤ) : ℝ :=
  w (kl.1+kl.2)*‖φ.val (kl.1+kl.2)‖ * (w (-kl.2-n)*‖f.val (-kl.2)‖)

/-- The weighted numerator moment converges and factors with the original scalar norms. -/
theorem sourceLemma65ProofNumerator_moment (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeff w.toWeight p) (n : ℤ) :
    Summable (fun kl => (sourceLemma65ProofNumerator w φ f n kl)^p.toReal) ∧
      (∑' kl, (sourceLemma65ProofNumerator w φ f n kl)^p.toReal) =
        ‖φ‖^p.toReal * (w.shiftedNorm (-n) f)^p.toReal := by
  let φW := WeightedCoeff.weightEquiv w.toWeight p φ
  let fW := Coeff.reindex (Equiv.neg ℤ)
    (WeightedCoeff.weightEquiv (w.toWeight.shift (-n)) p (w.toShift (-n) f))
  have he (kl : ℤ × ℤ) : sourceLemma65ProofNumerator w φ f n kl = ‖φW (kl.1+kl.2)‖*‖fW kl.2‖ := by
    simp only [sourceLemma65ProofNumerator,φW,fW,WeightedCoeff.weightEquiv_apply,Coeff.reindex_apply,
      Equiv.neg_apply,SpectralWeight.toShift_apply,Weight.shift_apply,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos (w.positive _),← sub_eq_add_neg]
  constructor
  · simpa only [he] using summable_lemma34NumeratorMoment hp φW fW
  · simp only [he]
    rw [lemma34NumeratorMoment_eq hp φW fW]
    simp only [fW,Coeff.norm_reindex]
    rfl

/-- The exact reciprocal product has a finite conjugate-exponent moment. -/
theorem sourceLemma65ProofReciprocal_moment (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    Summable (fun kl => (sourceLemma65ProofReciprocal n kl)^p.conjExponent.toReal) := by
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
  have hs := ((lp.memℓp a).summable hqpos).mul_of_nonneg ((lp.memℓp a).summable hqpos)
    (fun _ => by positivity) (fun _ => by positivity)
  simpa only [he,Real.mul_rpow (norm_nonneg _) (norm_nonneg _)] using hs

/-- The literal weighted Holder display on any selected region with a weight gain. -/
theorem sourceLemma65Proof_masked_holder (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ f : WeightedCoeff w.toWeight p) (n : ℤ) (S : Set (ℤ × ℤ)) {C : ℝ} (hC : 0 ≤ C)
    (hgain : ∀ kl ∈ S, w (kl.1-n) ≤ C*w (kl.1+kl.2)*w (-kl.2-n)) :
    (∑' kl, if kl ∈ S then sourceLemma65ProofTerm w φ f n kl else 0) ≤
      C * (∑' kl, if kl ∈ S then (sourceLemma65ProofReciprocal n kl)^p.conjExponent.toReal else 0)^(1/p.conjExponent.toReal) *
        (∑' kl, if kl ∈ S then (sourceLemma65ProofNumerator w φ f n kl)^p.toReal else 0)^(1/p.toReal) := by
  have hq : p.conjExponent ≠ ⊤ := ne_of_lt
    ((ENNReal.HolderConjugate.lt_top_iff_one_lt p.conjExponent p).mpr hp1)
  have hpq := ENNReal.HolderConjugate.toReal_of_ne_top hp hq
  let D := sourceLemma65ProofReciprocal n
  let B := sourceLemma65ProofNumerator w φ f n
  have hd (kl) : 0 ≤ D kl := by dsimp [D,sourceLemma65ProofReciprocal]; positivity
  have hb (kl) : 0 ≤ B kl := by dsimp [B,sourceLemma65ProofNumerator]; have h1 := w.positive (kl.1+kl.2); have h2 := w.positive (-kl.2-n); positivity
  have hds := sourceLemma65ProofReciprocal_moment hp hp1 n
  have hbs := (sourceLemma65ProofNumerator_moment hp w φ f n).1
  have hdm : Summable (fun kl => (if kl ∈ S then D kl else 0)^p.conjExponent.toReal) := by
    apply hds.of_nonneg_of_le (fun kl => Real.rpow_nonneg (by split_ifs; exact hd kl; exact le_rfl) _)
    intro kl; split_ifs
    · exact le_rfl
    · rw [Real.zero_rpow hpq.symm.pos.ne']; exact Real.rpow_nonneg (hd kl) _
  have hbm : Summable (fun kl => (if kl ∈ S then B kl else 0)^p.toReal) := by
    apply hbs.of_nonneg_of_le (fun kl => Real.rpow_nonneg (by split_ifs; exact hb kl; exact le_rfl) _)
    intro kl; split_ifs
    · exact le_rfl
    · rw [Real.zero_rpow hpq.pos.ne']; exact Real.rpow_nonneg (hb kl) _
  obtain ⟨hprod,hholder⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg hpq.symm
    (f := fun kl => if kl ∈ S then D kl else 0) (g := fun kl => if kl ∈ S then B kl else 0)
    (fun kl => by split_ifs <;> first | exact hd kl | exact le_rfl)
    (fun kl => by split_ifs <;> first | exact hb kl | exact le_rfl) hdm hbm
  have hpoint (kl : ℤ × ℤ) :
      (if kl ∈ S then sourceLemma65ProofTerm w φ f n kl else 0) ≤
        C*((if kl ∈ S then D kl else 0)*(if kl ∈ S then B kl else 0)) := by
    by_cases hS : kl ∈ S
    · simp only [hS,if_true]
      by_cases he : kl.1 = n ∨ kl.2 = n
      · simp only [sourceLemma65ProofTerm,if_pos he]; exact mul_nonneg hC (mul_nonneg (hd kl) (hb kl))
      · simp only [sourceLemma65ProofTerm,if_neg he,D,B,sourceLemma65ProofReciprocal,sourceLemma65ProofNumerator,div_eq_mul_inv]
        have hh := mul_le_mul_of_nonneg_right (hgain kl hS)
          (show 0 ≤ ‖φ.val (kl.1+kl.2)‖*‖f.val (-kl.2)‖*(|((n-kl.1:ℤ):ℝ)| * |((n-kl.2:ℤ):ℝ)|)⁻¹ by positivity)
        nlinarith only [hh]
    · simp only [hS,if_false,mul_zero,le_refl]
  have hnonneg (kl : ℤ × ℤ) : 0 ≤ (if kl ∈ S then sourceLemma65ProofTerm w φ f n kl else 0) := by
    split_ifs
    · dsimp [sourceLemma65ProofTerm]; split_ifs; exact le_rfl
      have hw := w.positive (kl.1-n); positivity
    · exact le_rfl
  have hm := (hprod.mul_left C).of_nonneg_of_le hnonneg hpoint
  have hsum1 := hm.tsum_le_tsum hpoint (hprod.mul_left C)
  rw [tsum_mul_left] at hsum1
  have hsum := hsum1.trans (mul_le_mul_of_nonneg_left hholder hC)
  have hpow (F : ℤ × ℤ → ℝ) (P : ℝ) (hP : P ≠ 0) (kl : ℤ × ℤ) :
      (if kl ∈ S then F kl else 0)^P = if kl ∈ S then (F kl)^P else 0 := by
    split_ifs <;> simp [Real.zero_rpow hP]
  simp only [hpow D _ hpq.symm.pos.ne',hpow B _ hpq.pos.ne'] at hsum
  simpa only [D,B,mul_assoc] using hsum

end NLS.ZakharovShabat

namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Restricting the exact weighted numerator moment costs no norm constant. -/
theorem sourceLemma65ProofNumerator_masked_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeff w.toWeight p) (n : ℤ) (S : Set (ℤ × ℤ)) :
    (∑' kl, if kl ∈ S then (sourceLemma65ProofNumerator w φ f n kl)^p.toReal else 0)^(1/p.toReal) ≤
      ‖φ‖*w.shiftedNorm (-n) f := by
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne' hp
  obtain ⟨hs,he⟩ := sourceLemma65ProofNumerator_moment hp w φ f n
  have hB (kl : ℤ × ℤ) : 0 ≤ sourceLemma65ProofNumerator w φ f n kl := by
    dsimp [sourceLemma65ProofNumerator]
    have h1 := w.positive (kl.1+kl.2); have h2 := w.positive (-kl.2-n); positivity
  have hn (kl) : 0 ≤ (sourceLemma65ProofNumerator w φ f n kl)^p.toReal := Real.rpow_nonneg (hB kl) _
  have hle (kl) : (if kl ∈ S then (sourceLemma65ProofNumerator w φ f n kl)^p.toReal else 0) ≤
      (sourceLemma65ProofNumerator w φ f n kl)^p.toReal := by split_ifs; exact le_rfl; exact hn kl
  have hm := hs.of_nonneg_of_le (fun kl => by split_ifs; exact hn kl; exact le_rfl) hle
  have h := Real.rpow_le_rpow (tsum_nonneg (fun kl => by split_ifs; exact hn kl; exact le_rfl))
    (hm.tsum_le_tsum hle hs) (by positivity : 0 ≤ 1/p.toReal)
  rw [he,← Real.mul_rpow (norm_nonneg _) (show 0 ≤ w.shiftedNorm (-n) f from norm_nonneg _),
    ← Real.rpow_mul (mul_nonneg (norm_nonneg _) (show 0 ≤ w.shiftedNorm (-n) f from norm_nonneg _)),
    mul_one_div_cancel hp0.ne',Real.rpow_one] at h
  exact h

/-- Submultiplicativity gives the far-region weight comparison. -/
theorem sourceLemma65Proof_submultiplicative (w : SpectralWeight) (n k l : ℤ) :
    w (k-n) ≤ w (k+l)*w (-l-n) := by
  simpa only [show k+l+(-l-n) = k-n by omega] using w.add_le (k+l) (-l-n)

/-- The exact far Holder display, retaining its selected numerator moment. -/
theorem sourceLemma65Proof_far_holder (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ f : WeightedCoeff w.toWeight p) (n : ℤ) :
    (∑' kl, if sourceLemma65ProofFar n kl.1 kl.2 then sourceLemma65ProofTerm w φ f n kl else 0) ≤
      (∑' kl, if sourceLemma65ProofFar n kl.1 kl.2 then (sourceLemma65ProofReciprocal n kl)^p.conjExponent.toReal else 0)^(1/p.conjExponent.toReal) *
      (∑' kl, if sourceLemma65ProofFar n kl.1 kl.2 then (sourceLemma65ProofNumerator w φ f n kl)^p.toReal else 0)^(1/p.toReal) := by
  simpa only [one_mul,Set.mem_ofPred_eq] using sourceLemma65Proof_masked_holder hp hp1 w φ f n
    {kl | sourceLemma65ProofFar n kl.1 kl.2} (C := 1) (by norm_num)
    (fun kl _ => by simpa only [one_mul] using sourceLemma65Proof_submultiplicative w n kl.1 kl.2)

/-- The exact near Holder display retains the additional factor 1/w(n). -/
theorem sourceLemma65Proof_near_holder (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ f : WeightedCoeff w.toWeight p) (n : ℤ) :
    (∑' kl, if sourceLemma65ProofNear n kl.1 kl.2 then sourceLemma65ProofTerm w φ f n kl else 0) ≤
      (1/w n) * (∑' kl, if sourceLemma65ProofNear n kl.1 kl.2 then (sourceLemma65ProofReciprocal n kl)^p.conjExponent.toReal else 0)^(1/p.conjExponent.toReal) *
      (∑' kl, if sourceLemma65ProofNear n kl.1 kl.2 then (sourceLemma65ProofNumerator w φ f n kl)^p.toReal else 0)^(1/p.toReal) := by
  apply sourceLemma65Proof_masked_holder hp hp1 w φ f n {kl | sourceLemma65ProofNear n kl.1 kl.2}
    (by have hw := w.positive n; positivity)
  intro kl hkl
  have h := (le_div_iff₀ (w.positive n)).mpr (sourceLemma65ProofNear_weight w hkl)
  simpa only [div_eq_mul_inv,one_mul,mul_comm,mul_left_comm,mul_assoc] using h

/-- Replacing the potential by the exact remainder leaves the entire near subsum unchanged. -/
theorem sourceLemma65Proof_near_tail_eq (w : SpectralWeight) (φ f : WeightedCoeff w.toWeight p) (n : ℤ) :
    (∑' kl, if sourceLemma65ProofNear n kl.1 kl.2 then sourceLemma65ProofTerm w
      (WeightedCoeff.fourierTail w.toWeight n.natAbs φ) f n kl else 0) =
    (∑' kl, if sourceLemma65ProofNear n kl.1 kl.2 then sourceLemma65ProofTerm w φ f n kl else 0) := by
  apply tsum_congr
  intro kl
  by_cases h : sourceLemma65ProofNear n kl.1 kl.2
  · simp only [h,if_true,sourceLemma65ProofTerm,sourceLemma65ProofNear_tail w φ h]
  · simp only [h,if_false]

/-- The far moment has the original potential norm and the oppositely shifted input norm. -/
theorem sourceLemma65Proof_far_holder_norm (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ f : WeightedCoeff w.toWeight p) (n : ℤ) :
    (∑' kl, if sourceLemma65ProofFar n kl.1 kl.2 then sourceLemma65ProofTerm w φ f n kl else 0) ≤
      (∑' kl, if sourceLemma65ProofFar n kl.1 kl.2 then (sourceLemma65ProofReciprocal n kl)^p.conjExponent.toReal else 0)^(1/p.conjExponent.toReal) *
        (‖φ‖*w.shiftedNorm (-n) f) := by
  exact (sourceLemma65Proof_far_holder hp hp1 w φ f n).trans (mul_le_mul_of_nonneg_left
    (sourceLemma65ProofNumerator_masked_le hp w φ f n {kl | sourceLemma65ProofFar n kl.1 kl.2}) (by unfold sourceLemma65ProofReciprocal; positivity))

/-- The near moment has the boundary-inclusive potential tail, divided by w(n). -/
theorem sourceLemma65Proof_near_holder_tail (hp : p ≠ ⊤) (hp1 : 1 < p) (w : SpectralWeight)
    (φ f : WeightedCoeff w.toWeight p) (n : ℤ) :
    (∑' kl, if sourceLemma65ProofNear n kl.1 kl.2 then sourceLemma65ProofTerm w φ f n kl else 0) ≤
      (1/w n) * (∑' kl, if sourceLemma65ProofNear n kl.1 kl.2 then (sourceLemma65ProofReciprocal n kl)^p.conjExponent.toReal else 0)^(1/p.conjExponent.toReal) *
        (‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ‖*w.shiftedNorm (-n) f) := by
  rw [← sourceLemma65Proof_near_tail_eq]
  apply (sourceLemma65Proof_near_holder hp hp1 w _ f n).trans
  apply mul_le_mul_of_nonneg_left (sourceLemma65ProofNumerator_masked_le hp w _ f n {kl | sourceLemma65ProofNear n kl.1 kl.2})
  have hw := w.positive n
  unfold sourceLemma65ProofReciprocal
  positivity

/-- Reflection gives the second physical orientation for every finite Banach exponent. -/
theorem sourceLemma65Proof_true_reflection (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeff w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    complementarySandwich hp w φ n z hz true f =
      w.reflection (complementarySandwich hp w (w.reflection φ) n z hz false (w.reflection f)) := by
  apply Subtype.ext
  funext j
  simp only [SpectralWeight.reflection_apply,complementarySandwich_apply,
    Bool.not_true,Bool.not_false,freeFrequency_false,freeFrequency_true]
  congr 1
  rw [← (Equiv.neg ℤ).tsum_eq (fun k : ℤ => φ.val (-(-j-k))*(complementarySymbol n z (-k)*f.val (-k)))]
  simp only [Equiv.neg_apply,neg_neg]
  apply tsum_congr
  intro k
  rw [show -(-j- -k) = j-k by omega]

/-- Both actual components of g satisfy the printed majorants in their original shifts. -/
theorem sourceLemma65Proof_original_majorants (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ f : WeightedCoeffPair w.toWeight p) (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    let t := weightedPotentialInverse hp w φ n z hz f
    w.shiftedNorm n (complementaryScalarL1 hp w.toWeight n z hz true t.fst) ≤
      (∑' kl, sourceLemma65ProofTerm w (w.reflection φ.fst) (w.reflection f.snd) n kl) ∧
    w.shiftedNorm (-n) (complementaryScalarL1 hp w.toWeight n z hz false t.snd) ≤
      (∑' kl, sourceLemma65ProofTerm w φ.snd f.fst n kl) := by
  have hm : complementaryScalarL1 hp w.toWeight n z hz true (weightedPotentialInverse hp w φ n z hz f).fst =
      complementarySandwich hp w φ.fst n z hz true f.snd := by
    apply Subtype.ext
    funext k
    simp [complementaryScalarL1_apply,complementarySandwich_apply,SpectralWeight.convolution_apply]
  have hp' : complementaryScalarL1 hp w.toWeight n z hz false (weightedPotentialInverse hp w φ n z hz f).snd =
      complementarySandwich hp w φ.snd n z hz false f.fst := by
    apply Subtype.ext
    funext k
    simp [complementaryScalarL1_apply,complementarySandwich_apply,SpectralWeight.convolution_apply]
  dsimp only
  rw [hm,hp',sourceLemma65Proof_true_reflection,SpectralWeight.shiftedNorm_reflection]
  exact ⟨sourceLemma65Proof_norm_le_literal hp w _ _ n z hz,sourceLemma65Proof_norm_le_literal hp w _ _ n z hz⟩

end NLS.ZakharovShabat

namespace NLS.ZakharovShabat

/-- The p=1 Holder endpoint uses a uniform bound for the reciprocal on the selected region. -/
theorem sourceLemma65Proof_masked_one (w : SpectralWeight) (φ f : WeightedCoeff w.toWeight 1)
    (n : ℤ) (S : Set (ℤ × ℤ)) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hgain : ∀ kl ∈ S, w (kl.1-n) ≤ C*w (kl.1+kl.2)*w (-kl.2-n))
    (hrecip : ∀ kl ∈ S, sourceLemma65ProofReciprocal n kl ≤ K) :
    (∑' kl, if kl ∈ S then sourceLemma65ProofTerm w φ f n kl else 0) ≤
      C*K*(‖φ‖*w.shiftedNorm (-n) f) := by
  let B := sourceLemma65ProofNumerator w φ f n
  have hb (kl) : 0 ≤ B kl := by
    dsimp [B,sourceLemma65ProofNumerator]
    have h1 := w.positive (kl.1+kl.2); have h2 := w.positive (-kl.2-n); positivity
  have hs : Summable B := by simpa [B] using (sourceLemma65ProofNumerator_moment (by simp) w φ f n).1
  have he : (∑' kl, B kl) = ‖φ‖*w.shiftedNorm (-n) f := by
    simpa [B] using (sourceLemma65ProofNumerator_moment (by simp) w φ f n).2
  have hle (kl) : (if kl ∈ S then sourceLemma65ProofTerm w φ f n kl else 0) ≤ C*K*B kl := by
    by_cases hS : kl ∈ S
    · simp only [hS,if_true]
      by_cases hn : kl.1 = n ∨ kl.2 = n
      · simp only [sourceLemma65ProofTerm,if_pos hn]
        exact mul_nonneg (mul_nonneg hC hK) (hb kl)
      · have hfirst : sourceLemma65ProofTerm w φ f n kl ≤ C * sourceLemma65ProofReciprocal n kl * B kl := by
          simp only [sourceLemma65ProofTerm,if_neg hn,sourceLemma65ProofReciprocal,B,sourceLemma65ProofNumerator,div_eq_mul_inv]
          have h := mul_le_mul_of_nonneg_right (hgain kl hS)
            (show 0 ≤ ‖φ.val (kl.1+kl.2)‖*‖f.val (-kl.2)‖*(|((n-kl.1:ℤ):ℝ)| * |((n-kl.2:ℤ):ℝ)|)⁻¹ by positivity)
          nlinarith only [h]
        exact hfirst.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hrecip kl hS) hC) (hb kl))
    · simp only [hS,if_false]
      exact mul_nonneg (mul_nonneg hC hK) (hb kl)
  have hm := (hs.mul_left (C*K)).of_nonneg_of_le (fun kl => by
    split_ifs
    · dsimp [sourceLemma65ProofTerm]; split_ifs; exact le_rfl
      have hw := w.positive (kl.1-n); positivity
    · exact le_rfl) hle
  have h := hm.tsum_le_tsum hle (hs.mul_left (C*K))
  rwa [tsum_mul_left,he] at h

/-- The punctures make the reciprocal product at most one everywhere. -/
theorem sourceLemma65ProofReciprocal_le_one (n k l : ℤ) : sourceLemma65ProofReciprocal n (k,l) ≤ 1 := by
  by_cases hk : k = n
  · simp [sourceLemma65ProofReciprocal,hk]
  by_cases hl : l = n
  · simp [sourceLemma65ProofReciprocal,hl]
  have hdist (j : ℤ) (hj : j ≠ n) : 1 ≤ |((n-j:ℤ):ℝ)| := by exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr (Ne.symm hj))
  have hprod : 1 ≤ |((n-k:ℤ):ℝ)| * |((n-l:ℤ):ℝ)| := by nlinarith [hdist k hk,hdist l hl]
  exact inv_le_one_of_one_le₀ hprod

/-- The near endpoint retains exactly the potential remainder and its inverse weight. -/
theorem sourceLemma65Proof_near_one (w : SpectralWeight) (φ f : WeightedCoeff w.toWeight 1) (n : ℤ) :
    (∑' kl, if sourceLemma65ProofNear n kl.1 kl.2 then sourceLemma65ProofTerm w φ f n kl else 0) ≤
      (1/w n)*(‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ‖*w.shiftedNorm (-n) f) := by
  rw [← sourceLemma65Proof_near_tail_eq]
  have h := sourceLemma65Proof_masked_one w (WeightedCoeff.fourierTail w.toWeight n.natAbs φ) f n
    {kl | sourceLemma65ProofNear n kl.1 kl.2} (C := 1/w n) (K := 1)
    (by have hw := w.positive n; positivity) (by norm_num) (fun kl hkl => ?_)
    (fun kl _ => sourceLemma65ProofReciprocal_le_one n kl.1 kl.2)
  · simpa only [mul_one,Set.mem_ofPred_eq] using h
  · have h := (le_div_iff₀ (w.positive n)).mpr (sourceLemma65ProofNear_weight w hkl)
    simpa only [div_eq_mul_inv,one_mul,mul_comm,mul_left_comm,mul_assoc] using h

end NLS.ZakharovShabat

namespace NLS.ZakharovShabat

/-- The strict far cutoff gives uniform reciprocal decay, also at the zero center. -/
theorem sourceLemma65ProofReciprocal_far (n k l : ℤ) (h : sourceLemma65ProofFar n k l) :
    sourceLemma65ProofReciprocal n (k,l) ≤ 2 / (1 + |(n : ℝ)|) := by
  have hdist (j : ℤ) (hj : j ≠ n) : 1 ≤ |((n-j : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr (Ne.symm hj))
  have hhalf (j : ℤ) (hj : |(n : ℝ)|/2 < |((n-j : ℤ) : ℝ)|) :
      1 + |(n : ℝ)| ≤ 2 * |((n-j : ℤ) : ℝ)| := by
    have he : |n| < 2 * |n-j| := by exact_mod_cast (by linarith : |(n : ℝ)| < 2 * |((n-j : ℤ) : ℝ)|)
    have hi : 1 + |n| ≤ 2 * |n-j| := by omega
    exact_mod_cast hi
  obtain ⟨hk,hl,hfar⟩ := h
  have hk1 := hdist k hk
  have hl1 := hdist l hl
  have hprod : (1+|(n : ℝ)|)/2 ≤ |((n-k : ℤ) : ℝ)| * |((n-l : ℤ) : ℝ)| := by
    rcases hfar with hkfar | hlfar
    · nlinarith [hhalf k hkfar]
    · nlinarith [hhalf l hlfar]
  have hpos : 0 < (1+|(n : ℝ)|)/2 := by positivity
  have hb := inv_anti₀ hpos hprod
  simpa only [sourceLemma65ProofReciprocal,inv_div,one_div] using hb

/-- The p=1 far subsum decays at every signed center with no loss of input shifts. -/
theorem sourceLemma65Proof_far_one (w : SpectralWeight) (φ f : WeightedCoeff w.toWeight 1) (n : ℤ) :
    (∑' kl, if sourceLemma65ProofFar n kl.1 kl.2 then sourceLemma65ProofTerm w φ f n kl else 0) ≤
      (2/(1+|(n : ℝ)|))*(‖φ‖*w.shiftedNorm (-n) f) := by
  simpa only [one_mul,Set.mem_ofPred_eq] using sourceLemma65Proof_masked_one w φ f n
    {kl | sourceLemma65ProofFar n kl.1 kl.2} (C := 1) (K := 2/(1+|(n : ℝ)|))
    (by norm_num) (by positivity)
    (fun kl _ => by simpa only [one_mul] using sourceLemma65Proof_submultiplicative w n kl.1 kl.2)
    (fun kl hkl => sourceLemma65ProofReciprocal_far n kl.1 kl.2 hkl)

/-- The literal p=1 series recombines into the far decay and exact near tail. -/
theorem sourceLemma65Proof_endpoint (w : SpectralWeight) (φ f : WeightedCoeff w.toWeight 1)
    (n : ℤ) (z : ℂ) (hz : z ∈ resonantStrip n) :
    w.shiftedNorm (-n) (complementarySandwich (by simp) w φ n z hz false f) ≤
      ((2/(1+|(n : ℝ)|))*‖φ‖ + ‖WeightedCoeff.fourierTail w.toWeight n.natAbs φ‖/w n)*
        w.shiftedNorm (-n) f := by
  apply (sourceLemma65Proof_norm_le_literal (by simp) w φ f n z hz).trans
  rw [sourceLemma65ProofTerm_split (by simp)]
  have h := add_le_add (sourceLemma65Proof_far_one w φ f n) (sourceLemma65Proof_near_one w φ f n)
  convert h using 1; ring

end NLS.ZakharovShabat
