import NLS.ZakharovShabat.SpectralLocalization
import NLS.ComplexAnalysis.EntireEvenSquareDescent

/-! Squaring the positive auxiliary frequency disks preserves strict real
order and separates them from the ENTIRE squared central box. No reality
assumption on the frequencies is used. -/
noncomputable section
open Set Complex Metric
namespace NLS.ZakharovShabat

/-- A square root can always be chosen in the closed right half-plane. -/
theorem exists_square_root_re_nonneg (e : ℂ) :
    ∃ z : ℂ, z^2 = e ∧ 0 ≤ z.re := by
  by_cases h : 0 ≤ (Complex.sqrt e).re
  · exact ⟨Complex.sqrt e,NLS.ComplexAnalysis.complex_sqrt_sq e,h⟩
  · exact ⟨-Complex.sqrt e,by rw [neg_sq,NLS.ComplexAnalysis.complex_sqrt_sq],
      by simpa only [Complex.neg_re] using (neg_nonneg.mpr (le_of_not_ge h))⟩

/-- A quarter-pi frequency disk controls both original real coordinates. -/
theorem frequencyDisk_coordinate_bounds (n : ℤ) (z : ℂ)
    (hz : z ∈ ball ((Real.pi:ℂ)*n) (Real.pi/4)) :
    |z.re-Real.pi*n| < Real.pi/4 ∧ |z.im| < Real.pi/4 := by
  rw [mem_ball,dist_eq_norm] at hz
  have hr := (Complex.abs_re_le_norm (z-(Real.pi:ℂ)*n)).trans_lt hz
  have hi := (Complex.abs_im_le_norm (z-(Real.pi:ℂ)*n)).trans_lt hz
  simpa only [Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.intCast_re,Complex.intCast_im,
    mul_zero,zero_mul,sub_zero,add_zero] using And.intro hr hi

/-- Every positive-index frequency in its disk has strictly positive real part. -/
theorem re_pos_of_mem_positive_frequencyDisk (n : ℕ) (hn : 0 < n) (z : ℂ)
    (hz : z ∈ ball ((Real.pi:ℂ)*n) (Real.pi/4)) : 0 < z.re := by
  have hb := (frequencyDisk_coordinate_bounds (n:ℤ) z hz).1
  simp only [Int.cast_natCast] at hb
  have hl := (abs_lt.mp hb).1
  have hnp : (1:ℝ) ≤ n := by exact_mod_cast hn
  nlinarith [Real.pi_pos,mul_le_mul_of_nonneg_left hnp Real.pi_pos.le]

/-- A real coordinate separated from a symmetric strip by the imaginary
radius retains strict real order after squaring. -/
theorem re_sq_lt_re_sq_of_coordinate_separation (z w : ℂ) (A r : ℝ)
    (hA : 0 < A) (hr : 0 ≤ r) (hz : |z.re| < A)
    (hw : A+r < w.re) (hi : |w.im| ≤ r) : (z^2).re < (w^2).re := by
  have hzs : z.re^2 < A^2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg z.re) hA.le).mpr hz
  have hws : (A+r)^2 < w.re^2 :=
    (sq_lt_sq₀ (by linarith) (by linarith)).mpr hw
  have his : w.im^2 ≤ r^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg w.im) hr).mpr hi
  simp only [pow_two,Complex.mul_re]
  nlinarith [sq_nonneg z.im,mul_nonneg hA.le hr]

/-- EVERY squared central frequency precedes EVERY squared positive high
frequency at the original cutoff, including nonreal frequencies. -/
theorem re_sq_central_lt_positive_frequencyDisk (N n : ℕ) (hn : N < n)
    (z w : ℂ) (hz : z ∈ centralSpectralBox N)
    (hw : w ∈ ball ((Real.pi:ℂ)*n) (Real.pi/4)) : (z^2).re < (w^2).re := by
  have hb := frequencyDisk_coordinate_bounds (n:ℤ) w hw
  simp only [Int.cast_natCast] at hb
  apply re_sq_lt_re_sq_of_coordinate_separation z w
    ((N:ℝ)*Real.pi+Real.pi/2) (Real.pi/4) (by positivity)
    (by positivity) hz.1 ?_ hb.2.le
  have hnn : (N:ℝ)+1 ≤ n := by exact_mod_cast hn
  have hm := mul_le_mul_of_nonneg_left hnn Real.pi_pos.le
  have hl := (abs_lt.mp hb.1).1
  nlinarith [Real.pi_pos]

/-- Squaring ANY two distinct positive frequency disks preserves their
strict real order. This includes every complex high-frequency branch. -/
theorem re_sq_lt_of_positive_frequencyDisks (i j : ℕ) (hij : i < j)
    (z w : ℂ) (hz : z ∈ ball ((Real.pi:ℂ)*i) (Real.pi/4))
    (hw : w ∈ ball ((Real.pi:ℂ)*j) (Real.pi/4)) : (z^2).re < (w^2).re := by
  have hbz := frequencyDisk_coordinate_bounds (i:ℤ) z hz
  have hbw := frequencyDisk_coordinate_bounds (j:ℤ) w hw
  simp only [Int.cast_natCast] at hbz hbw
  apply re_sq_lt_re_sq_of_coordinate_separation z w
    (Real.pi*i+Real.pi/4) (Real.pi/4) (by positivity) (by positivity) ?_ ?_ hbw.2.le
  · have ht : |z.re| ≤ |z.re-Real.pi*i|+Real.pi*i := by
      calc
        _ = |(z.re-Real.pi*i)+Real.pi*i| := by congr 1; ring
        _ ≤ |z.re-Real.pi*i|+|Real.pi*i| := abs_add_le _ _
        _ = _ := by rw [abs_of_nonneg (by positivity : 0 ≤ Real.pi*(i:ℝ))]
    linarith [hbz.1]
  · have hnn : (i:ℝ)+1 ≤ j := by exact_mod_cast hij
    have hm := mul_le_mul_of_nonneg_left hnn Real.pi_pos.le
    have hl := (abs_lt.mp hbw.1).1
    nlinarith [Real.pi_pos]

end NLS.ZakharovShabat
