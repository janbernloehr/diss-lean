import NLS.SequenceSpaces.SpectralWeightProduct
import NLS.SequenceSpaces.SpectralWeightInterpolation
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section
set_option autoImplicit false
namespace NLS.SpectralWeight

def corollarySplit (s : ℝ) : ℝ := min s (1/2)

theorem corollarySplit_bounds (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ corollarySplit s ∧ corollarySplit s ≤ 1/2 ∧ corollarySplit s ≤ s :=
  ⟨le_min hs (by norm_num),min_le_right _ _,min_le_left _ _⟩

def corollaryWeight (s : ℝ) (hs : 0 ≤ s) : SpectralWeight :=
  product (sobolev (corollarySplit s) (corollarySplit_bounds s hs).1)
    (piSobolev (s-corollarySplit s) (sub_nonneg.mpr (corollarySplit_bounds s hs).2.2))

theorem corollaryWeight_le (s : ℝ) (hs : 0 ≤ s) (k : ℤ) :
    corollaryWeight s hs k ≤ piSobolev s hs k := by
  let r := corollarySplit s
  have hr : 0 ≤ r := (corollarySplit_bounds s hs).1
  have hb : 1+|(k : ℝ)| ≤ 1+|(k : ℝ)*Real.pi| := by
    rw [abs_mul,abs_of_pos Real.pi_pos]
    nlinarith [abs_nonneg (k : ℝ),Real.pi_gt_three]
  simp only [corollaryWeight,product_apply,sobolev_apply,Weight.sobolev_apply,piSobolev_apply]
  change (1+|(k : ℝ)|)^r*(1+|(k : ℝ)*Real.pi|)^(s-r) ≤
    (1+|(k : ℝ)*Real.pi|)^s
  calc
    _ ≤ (1+|(k : ℝ)*Real.pi|)^r*(1+|(k : ℝ)*Real.pi|)^(s-r) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hb hr) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

theorem corollaryWeight_homogeneous (s : ℝ) (hs : 0 ≤ s) (n : ℕ) :
    (2*Real.pi*(n : ℝ))^s ≤
      Real.pi^(corollarySplit s)*corollaryWeight s hs (2*(n : ℤ)) := by
  let r := corollarySplit s
  have hr : 0 ≤ r := (corollarySplit_bounds s hs).1
  have hsr : 0 ≤ s-r := sub_nonneg.mpr (corollarySplit_bounds s hs).2.2
  have h1 : (2*Real.pi*(n : ℝ))^r ≤ Real.pi^r*(1+2*(n : ℝ))^r := by
    rw [← Real.mul_rpow Real.pi_pos.le (by positivity)]
    exact Real.rpow_le_rpow (by positivity) (by nlinarith [Real.pi_pos]) hr
  have h2 : (2*Real.pi*(n : ℝ))^(s-r) ≤ (1+2*(n : ℝ)*Real.pi)^(s-r) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith) hsr
  have hh := mul_le_mul h1 h2 (by positivity) (by positivity)
  rw [← Real.rpow_add_of_nonneg (by positivity) hr hsr] at hh
  simp only [corollaryWeight,product_apply,sobolev_apply,Weight.sobolev_apply,
    piSobolev_apply,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast,
    abs_of_nonneg (by positivity : 0 ≤ 2*(n : ℝ)),
    abs_of_nonneg (by positivity : 0 ≤ 2*(n : ℝ)*Real.pi)]
  dsimp only [r] at hh
  have he : corollarySplit s+(s-corollarySplit s) = s := by ring
  rw [he] at hh
  simpa only [mul_assoc] using hh

theorem corollary_exponent (s : ℝ) (_hs : 0 ≤ s) :
    s*(3/2-corollarySplit s) ≤ max 1 s := by
  by_cases h : s ≤ 1/2
  · rw [corollarySplit,min_eq_left h]
    have hm : 1 ≤ max 1 s := le_max_left _ _
    nlinarith [sq_nonneg (s-1/2)]
  · rw [corollarySplit,min_eq_right (le_of_not_ge h)]
    norm_num

theorem corollaryWeight_extension_bound (s : ℝ) (hs : 0 ≤ s) (t : ℝ) (ht : 0 ≤ t) :
    (corollaryWeight s hs).realExtension t ≤ (1+Real.pi)^s*(1+t)^s := by
  apply ((corollaryWeight s hs).realExtension_bounds t).2.trans
  apply (corollaryWeight_le s hs ((⌊|t|⌋₊ : ℤ)+1)).trans
  rw [piSobolev_apply]
  have hf : (⌊|t|⌋₊ : ℝ) ≤ t := by simpa only [abs_of_nonneg ht] using Nat.floor_le ht
  have hb : 1+|((((⌊|t|⌋₊ : ℤ)+1 : ℤ) : ℝ))*Real.pi| ≤ (1+Real.pi)*(1+t) := by
    push_cast
    rw [abs_of_nonneg (by positivity : 0 ≤ ((⌊|t|⌋₊ : ℝ)+1)*Real.pi)]
    nlinarith [Real.pi_pos]
  exact (Real.rpow_le_rpow (by positivity) hb hs).trans_eq
    (Real.mul_rpow (by positivity) (by positivity))

theorem corollaryWeight_polynomial_bound (s : ℝ) (hs : 0 ≤ s) (Q : ℝ) (hQ : 0 ≤ Q) :
    (1+Q)+(corollaryWeight s hs).realExtension (16*Q^(3/2-corollarySplit s)) ≤
      (1+(17*(1+Real.pi))^s)*(1+Q)^(max 1 s) := by
  let a := 3/2-corollarySplit s
  have ha : 0 ≤ a := by dsimp [a]; linarith [(corollarySplit_bounds s hs).2.1]
  have hbase : 1 ≤ 1+Q := by linarith
  have hE : 1 ≤ (1+Q)^a := Real.one_le_rpow hbase ha
  have hQpow : Q^a ≤ (1+Q)^a := Real.rpow_le_rpow hQ (by linarith) ha
  have hpow : (1+16*Q^a)^s ≤ 17^s*(1+Q)^(a*s) := by
    calc
      _ ≤ (17*(1+Q)^a)^s := Real.rpow_le_rpow (by positivity) (by linarith) hs
      _ = _ := by rw [Real.mul_rpow (by norm_num) (by positivity),← Real.rpow_mul (by positivity)]
  have hExp : a*s ≤ max 1 s := by simpa only [a,mul_comm] using corollary_exponent s hs
  have hpowE := Real.rpow_le_rpow_of_exponent_le hbase hExp
  have ht := corollaryWeight_extension_bound s hs (16*Q^a) (by positivity)
  have hmul := mul_le_mul_of_nonneg_left (hpow.trans
    (mul_le_mul_of_nonneg_left hpowE (by positivity)))
      (by positivity : 0 ≤ (1+Real.pi)^s)
  have hlin : 1+Q ≤ (1+Q)^(max 1 s) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hbase (le_max_left (1 : ℝ) s)
  have hC : (1+Real.pi)^s*17^s = (17*(1+Real.pi))^s := by
    rw [← Real.mul_rpow (by positivity) (by norm_num)]; congr 1; ring
  dsimp only [a] at ht hmul
  rw [← mul_assoc,hC] at hmul
  nlinarith

end NLS.SpectralWeight
