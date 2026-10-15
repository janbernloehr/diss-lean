import NLS.SequenceSpaces.FiniteInterpolationSharp
import NLS.SequenceSpaces.ConjugateDuality
import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Sharp interpolation for finite matrices

Arbitrary finite input and output indices carry their genuine PiLp norms. Entire
power families give the exact geometric three-lines constant; norming tests
detect the finite conjugate norm. Extension by zero preserves every finite norm.
-/

noncomputable section
open Complex Set MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate
namespace NLS.FiniteMatrix
open NLS.Coeff
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The complex bilinear pairing of a finite matrix with input and test vectors. -/
def pair (K : κ → ι → ℂ) (a : ι → ℂ) (b : κ → ℂ) : ℂ := ∑ i, ∑ j, a i*K j i*b j

theorem norm_power_le_one {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    (hp : 0 < p.toReal) (hr : 0 < r.toReal) (a : ι → ℂ)
    (ha : ‖WithLp.toLp r a‖ ≤ 1) {w : ℂ} (hw : w.re = r.toReal / p.toReal) :
    ‖WithLp.toLp p (fun i => powerCurve (a i) w)‖ ≤ 1 := by
  have hpos : 0 < w.re := by rw [hw]; exact div_pos hr hp
  have hsum : (∑ i, ‖a i‖^r.toReal) ≤ 1 := by
    have h := Real.rpow_le_one (norm_nonneg (WithLp.toLp r a)) ha hr.le
    rw [PiLp.norm_eq_sum hr,← Real.rpow_mul (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)),
      one_div_mul_cancel hr.ne',Real.rpow_one] at h
    exact h
  rw [PiLp.norm_eq_sum hp]
  simp_rw [norm_powerCurve _ _ hpos,← Real.rpow_mul (norm_nonneg _),hw,div_mul_cancel₀ _ hp.ne']
  exact Real.rpow_le_one (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)) hsum (by positivity)

theorem norm_power_apply_le_one {r : ℝ≥0∞} [Fact (1 ≤ r)] (a : ι → ℂ)
    (ha : ‖WithLp.toLp r a‖ ≤ 1) {w : ℂ} (hw : 0 < w.re) (i : ι) :
    ‖powerCurve (a i) w‖ ≤ 1 := by
  rw [norm_powerCurve _ _ hw]
  exact Real.rpow_le_one (norm_nonneg _) ((PiLp.norm_apply_le (WithLp.toLp r a) i).trans ha) hw.le

/-- Three-lines interpolation with the exact geometric constant on unit balls. -/
theorem norm_pair_interpolate_unit
    {p₀ p₁ q₀ q₁ r s : ℝ≥0∞}
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]
    [Fact (1 ≤ r)] [Fact (1 ≤ s)]
    (hp₀ : 0 < p₀.toReal) (hp₁ : 0 < p₁.toReal)
    (hq₀ : 0 < q₀.toReal) (hq₁ : 0 < q₁.toReal)
    (hr : 0 < r.toReal) (hs : 0 < s.toReal)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hrt : r.toReal * ((1-t)/p₀.toReal + t/p₁.toReal) = 1)
    (hst : s.toReal * ((1-t)/q₀.toReal + t/q₁.toReal) = 1)
    (K : κ → ι → ℂ) {B₀ B₁ : ℝ} (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (h₀ : ∀ a b, ‖pair K a b‖ ≤ B₀ * ‖WithLp.toLp p₀ a‖ * ‖WithLp.toLp q₀ b‖)
    (h₁ : ∀ a b, ‖pair K a b‖ ≤ B₁ * ‖WithLp.toLp p₁ a‖ * ‖WithLp.toLp q₁ b‖)
    (a : ι → ℂ) (b : κ → ℂ) (ha : ‖WithLp.toLp r a‖ ≤ 1)
    (hb : ‖WithLp.toLp s b‖ ≤ 1) : ‖pair K a b‖ ≤ B₀^(1-t)*B₁^t := by
  let A := fun z i => powerCurve (a i) (interpolationWeight r.toReal p₀.toReal p₁.toReal z)
  let B := fun z j => powerCurve (b j) (interpolationWeight s.toReal q₀.toReal q₁.toReal z)
  let F := fun z => pair K (A z) (B z)
  have hd : Differentiable ℂ F := by
    apply Differentiable.fun_sum
    intro i _
    apply Differentiable.fun_sum
    intro j _
    exact (((differentiable_powerCurve (a i)).comp (differentiable_interpolationWeight _ _ _)).mul_const (K j i)).mul
      ((differentiable_powerCurve (b j)).comp (differentiable_interpolationWeight _ _ _))
  have hbound : BddAbove ((norm ∘ F) '' HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨∑ i, ∑ j, ‖K j i‖, ?_⟩
    rintro _ ⟨z,hz,rfl⟩
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro j _
    rw [norm_mul,norm_mul]
    calc
      _ ≤ 1*‖K j i‖*1 := by
        gcongr
        · exact norm_power_apply_le_one a ha (interpolationWeight_re_pos hr hp₀ hp₁ hz.1 hz.2) i
        · exact norm_power_apply_le_one b hb (interpolationWeight_re_pos hs hq₀ hq₁ hz.1 hz.2) j
      _ = _ := by ring
  have he₀ (z : ℂ) (hz : z.re = 0) : ‖F z‖ ≤ B₀ := by
    have hA : ‖WithLp.toLp p₀ (A z)‖ ≤ 1 :=
      norm_power_le_one hp₀ hr a ha (by rw [interpolationWeight_re,hz]; ring)
    have hB : ‖WithLp.toLp q₀ (B z)‖ ≤ 1 :=
      norm_power_le_one hq₀ hs b hb (by rw [interpolationWeight_re,hz]; ring)
    exact (h₀ (A z) (B z)).trans (by
      calc
        _ ≤ B₀*1*1 := by gcongr
        _ = B₀ := by ring)
  have he₁ (z : ℂ) (hz : z.re = 1) : ‖F z‖ ≤ B₁ := by
    have hA : ‖WithLp.toLp p₁ (A z)‖ ≤ 1 :=
      norm_power_le_one hp₁ hr a ha (by rw [interpolationWeight_re,hz]; ring)
    have hB : ‖WithLp.toLp q₁ (B z)‖ ≤ 1 :=
      norm_power_le_one hq₁ hs b hb (by rw [interpolationWeight_re,hz]; ring)
    exact (h₁ (A z) (B z)).trans (by
      calc
        _ ≤ B₁*1*1 := by gcongr
        _ = B₁ := by ring)
  have hthree := HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁' F
    (z := (t : ℂ)) ⟨ht₀,ht₁⟩ hd.diffContOnCl hbound he₀ he₁
  have ht : F (t : ℂ) = pair K a b := by
    dsimp [F,A,B]
    rw [interpolationWeight_at hrt,interpolationWeight_at hst]
    simp only [powerCurve_one]
  rwa [ht,ofReal_re] at hthree

theorem pair_smul (K : κ → ι → ℂ) (a : ι → ℂ) (b : κ → ℂ) (c d : ℂ) :
    pair K (c • a) (d • b) = c*d*pair K a b := by
  simp only [pair,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Homogeneous sharp interpolation for arbitrary finite input and test vectors. -/
theorem norm_pair_interpolate
    {p₀ p₁ q₀ q₁ r s : ℝ≥0∞}
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]
    [Fact (1 ≤ r)] [Fact (1 ≤ s)]
    (hp₀ : 0 < p₀.toReal) (hp₁ : 0 < p₁.toReal)
    (hq₀ : 0 < q₀.toReal) (hq₁ : 0 < q₁.toReal)
    (hr : 0 < r.toReal) (hs : 0 < s.toReal)
    {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (hrt : r.toReal * ((1-t)/p₀.toReal + t/p₁.toReal) = 1)
    (hst : s.toReal * ((1-t)/q₀.toReal + t/q₁.toReal) = 1)
    (K : κ → ι → ℂ) {B₀ B₁ : ℝ} (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (h₀ : ∀ a b, ‖pair K a b‖ ≤ B₀ * ‖WithLp.toLp p₀ a‖ * ‖WithLp.toLp q₀ b‖)
    (h₁ : ∀ a b, ‖pair K a b‖ ≤ B₁ * ‖WithLp.toLp p₁ a‖ * ‖WithLp.toLp q₁ b‖)
    (a : ι → ℂ) (b : κ → ℂ) :
    ‖pair K a b‖ ≤ (B₀^(1-t)*B₁^t)*‖WithLp.toLp r a‖*‖WithLp.toLp s b‖ := by
  by_cases ha : a = 0
  · simp [ha,pair]
  by_cases hb : b = 0
  · simp [hb,pair]
  have han : 0 < ‖WithLp.toLp r a‖ := by
    apply norm_pos_iff.mpr
    intro he
    apply ha
    exact congrArg WithLp.ofLp he
  have hbn : 0 < ‖WithLp.toLp s b‖ := by
    apply norm_pos_iff.mpr
    intro he
    apply hb
    exact congrArg WithLp.ofLp he
  let c : ℂ := (‖WithLp.toLp r a‖ : ℂ)⁻¹
  let d : ℂ := (‖WithLp.toLp s b‖ : ℂ)⁻¹
  have hc : ‖c‖ = ‖WithLp.toLp r a‖⁻¹ := by simp [c,norm_inv,Complex.norm_real]
  have hd : ‖d‖ = ‖WithLp.toLp s b‖⁻¹ := by simp [d,norm_inv,Complex.norm_real]
  have hna : ‖WithLp.toLp r (c • a)‖ ≤ 1 := by
    change ‖c • WithLp.toLp r a‖ ≤ 1
    rw [norm_smul,hc,inv_mul_cancel₀ han.ne']
  have hnb : ‖WithLp.toLp s (d • b)‖ ≤ 1 := by
    change ‖d • WithLp.toLp s b‖ ≤ 1
    rw [norm_smul,hd,inv_mul_cancel₀ hbn.ne']
  have h := norm_pair_interpolate_unit hp₀ hp₁ hq₀ hq₁ hr hs ht₀ ht₁ hrt hst K hB₀ hB₁ h₀ h₁
    (c • a) (d • b) hna hnb
  rw [pair_smul,norm_mul,norm_mul,hc,hd] at h
  have h' := mul_le_mul_of_nonneg_left h (mul_nonneg han.le hbn.le)
  have he : (‖WithLp.toLp r a‖*‖WithLp.toLp s b‖)*
      (‖WithLp.toLp r a‖⁻¹*‖WithLp.toLp s b‖⁻¹*‖pair K a b‖) = ‖pair K a b‖ := by field_simp
  rw [he] at h'
  nlinarith only [h']

open scoped ComplexConjugate NNReal

/-- A finite conjugate-norm test attaining the norm, with the complex phase included. -/
theorem exists_norming_test {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderConjugate q]
    (hp : 0 < p.toReal) (hq : 0 < q.toReal) (a : ι → ℂ) :
    ∃ b : ι → ℂ, ‖WithLp.toLp q b‖ ≤ 1 ∧ ∑ i, a i*b i = (‖WithLp.toLp p a‖ : ℂ) := by
  have hpq : p.toReal.HolderConjugate q.toReal := by
    simpa using ENNReal.HolderTriple.toReal 1 hp hq
  obtain ⟨g,hg,he⟩ := (NNReal.isGreatest_Lp Finset.univ (fun i => ‖a i‖₊) hpq).1
  let b := fun i => (g i : ℂ)*(conj (a i)/(‖a i‖:ℂ))
  have hphase (z : ℂ) : ‖conj z/(‖z‖:ℂ)‖ ≤ 1 := by
    by_cases hz : z = 0
    · simp [hz]
    · simp [Complex.norm_real,hz]
  have hbn (i : ι) : ‖b i‖ ≤ (g i : ℝ) := by
    dsimp [b]
    rw [norm_mul]
    calc
      _ ≤ ‖(g i : ℂ)‖*1 := mul_le_mul_of_nonneg_left (hphase _) (norm_nonneg _)
      _ = _ := by simp
  have hbnorm : ‖WithLp.toLp q b‖ ≤ 1 := by
    rw [PiLp.norm_eq_sum hq]
    apply Real.rpow_le_one (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (norm_nonneg _) _)) _ (by positivity)
    calc
      _ ≤ ∑ i, (g i : ℝ)^q.toReal := by
        apply Finset.sum_le_sum
        intro i _
        exact Real.rpow_le_rpow (norm_nonneg _) (hbn i) hq.le
      _ ≤ 1 := by exact_mod_cast hg
  have hnorm : ‖WithLp.toLp p a‖ = ∑ i, ‖a i‖*(g i : ℝ) := by
    rw [PiLp.norm_eq_sum hp]
    have he' := congrArg (fun x : ℝ≥0 => (x : ℝ)) he
    simpa only [NNReal.coe_sum,NNReal.coe_mul,coe_nnnorm,NNReal.coe_rpow] using he'.symm
  refine ⟨b,hbnorm,?_⟩
  rw [hnorm,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hmul (z : ℂ) : z*(conj z/(‖z‖:ℂ)) = (‖z‖:ℂ) := by
    by_cases hz : z = 0
    · simp [hz]
    · rw [← mul_div_assoc,Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_pow,
        pow_two,mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))]
  dsimp [b]
  rw [mul_left_comm,hmul,Complex.ofReal_mul]
  ring

end NLS.FiniteMatrix

namespace NLS.FiniteMatrix
variable {ι κ : Type*}

/-- Place a finite vector in a larger index space and set all other coordinates to zero. -/
def extendZero (e : ι ↪ κ) (a : ι → ℂ) : κ → ℂ := Function.extend e a 0

@[simp] theorem extendZero_apply (e : ι ↪ κ) (a : ι → ℂ) (i : ι) :
    extendZero e a (e i) = a i := e.injective.extend_apply a 0 i

theorem extendZero_apply_of_notMem (e : ι ↪ κ) (a : ι → ℂ) (k : κ) (hk : k ∉ Set.range e) :
    extendZero e a k = 0 := Function.extend_apply' a (0 : κ → ℂ) k hk

variable [Fintype ι] [Fintype κ]

theorem sum_extendZero {M : Type*} [AddCommMonoid M] (e : ι ↪ κ) (a : ι → ℂ)
    (f : ℂ → M) (hf : f 0 = 0) :
    (∑ k, f (extendZero e a k)) = ∑ i, f (a i) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e))]
  · simp only [Finset.sum_map,extendZero_apply]
  · intro k _ hk
    rw [extendZero_apply_of_notMem, hf]
    rintro ⟨i,hi⟩
    exact hk (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,hi⟩)

theorem norm_extendZero {p : ℝ≥0∞} (hp : 0 < p.toReal) (e : ι ↪ κ) (a : ι → ℂ) :
    ‖WithLp.toLp p (extendZero e a)‖ = ‖WithLp.toLp p a‖ := by
  rw [PiLp.norm_eq_sum hp,PiLp.norm_eq_sum hp]
  congr 1
  exact sum_extendZero e a (fun z => ‖z‖^p.toReal) (by simp [hp.ne'])

theorem sum_extendZero_mul (e : ι ↪ κ) (a : ι → ℂ) (g : κ → ℂ) :
    (∑ k, extendZero e a k*g k) = ∑ i, a i*g (e i) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e))]
  · simp only [Finset.sum_map,extendZero_apply]
  · intro k _ hk
    rw [extendZero_apply_of_notMem, zero_mul]
    rintro ⟨i,hi⟩
    exact hk (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,hi⟩)

end NLS.FiniteMatrix
