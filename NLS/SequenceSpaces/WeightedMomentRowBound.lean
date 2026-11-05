import NLS.SequenceSpaces.SquaredGapMomentMajorant
import NLS.SequenceSpaces.PositiveWeightedMomentKernel
import NLS.SequenceSpaces.PositiveSquaredGapMomentSummability

/-! Summing the actual squared-gap matrix bound retains an lp
majorant in the row index after the exact inverse-index weight. -/
noncomputable section
open Set Complex
open scoped ENNReal Classical
namespace NLS.Coeff
variable {p : ℝ≥0∞}

theorem norm_puncturedLattice_positive_difference (hp : 1 < p) (n m : ℕ+) (hmn : m ≠ n) :
    ‖puncturedLattice p hp (((n:ℕ):ℤ)-((m:ℕ):ℤ))‖=1/|((n:ℕ):ℝ)-(m:ℕ)| := by
  have hne : ((n:ℕ):ℤ)-((m:ℕ):ℤ) ≠ 0 := by
    intro he
    have h : (n:ℕ)=(m:ℕ) := Int.ofNat.inj (sub_eq_zero.mp he)
    exact hmn (PNat.coe_injective h.symm)
  rw [puncturedLattice_apply,if_neg hne,norm_inv,Complex.norm_intCast]
  simp only [Int.cast_sub,Int.cast_natCast,one_div]

variable [Fact (1 ≤ p)]

theorem norm_weighted_positive_moment_row_le (hp : 1 < p) (g : Coeff 2)
    (u : ℕ+ → ℕ+ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hu : ∀ n m : ℕ+, ‖u n m‖ ≤ B*‖g ((m:ℕ):ℤ)‖^2*
      (if m=n then 1 else 1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ))) (n : ℕ+) :
    ‖((n:ℕ):ℂ)⁻¹*(∑' m : ℕ+, ((m:ℕ):ℂ)*u n m)‖ ≤
      B*‖squaredGapMomentMajorant hp g ((n:ℕ):ℤ)‖ := by
  let b := squaredGapMagnitude g
  let κ := puncturedLattice p hp
  let j : ℕ+ → ℤ := fun m => ((m:ℕ):ℤ)
  have hj : Function.Injective j := by intro i j h; exact PNat.coe_injective (Int.ofNat.inj h)
  have hb (k : ℤ) : ‖b k‖=‖g k‖^2 := by
    rw [show b k=(‖g k‖^2:ℝ) from squaredGapMagnitude_apply g k,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
  have hsraw : Summable (fun m : ℕ+ => ‖((m:ℕ):ℂ)*u n m‖) :=
    summable_norm_positive_weighted_of_squared_gap_tail g n (u n) 0 B hB
      (fun m _ hmn => by simpa only [if_neg hmn] using hu n m)
  have hsw : Summable (fun m : ℕ+ => (((m:ℕ):ℝ)/(n:ℕ))*‖u n m‖) := by
    convert! hsraw.mul_left (1/((n:ℕ):ℝ)) using 1
    funext m
    simp only [norm_mul,Complex.norm_natCast]
    ring
  have hbZ : Summable (fun k : ℤ => ‖b k‖) := (lp.memℓp b).norm.summable_of_one
  have hbP : Summable (fun m : ℕ+ => ‖b (j m)‖) := hbZ.comp_injective hj
  have hcZ : Summable (fun k : ℤ => ‖κ (j n-k)‖*‖b k‖) := by
    apply (hbZ.mul_left ‖κ‖).of_nonneg_of_le (fun _ => by positivity)
    intro k
    exact mul_le_mul_of_nonneg_right (lp.norm_apply_le_norm (ne_of_gt (zero_lt_one.trans hp)) κ _) (norm_nonneg _)
  have hcP : Summable (fun m : ℕ+ => ‖κ (j n-j m)‖*‖b (j m)‖) := hcZ.comp_injective hj
  let d : ℕ+ → ℝ := fun m => if m=n then ‖b (j n)‖ else 0
  have hd : Summable d := summable_of_ne_finset_zero (s := {n}) (by
    intro m hm
    have hmn : m ≠ n := by simpa only [Finset.mem_singleton] using hm
    exact if_neg hmn)
  have hdSum : (∑' m : ℕ+, d m)=‖b (j n)‖ := by
    rw [tsum_eq_single n (by intro m hm; simp [d,hm])]
    simp only [d,if_pos rfl]
  have hcSum : (∑' m : ℕ+, ‖κ (j n-j m)‖*‖b (j m)‖) ≤
      ‖convolution (magnitude κ) (magnitude b) (j n)‖ := by
    rw [norm_magnitude_convolution_apply]
    exact tsum_comp_le_tsum_of_inj hcZ (fun _ => by positivity) hj
  have hbSum : (∑' m : ℕ+, ‖b (j m)‖) ≤ ‖b‖ := by
    have he : (∑' k : ℤ, ‖b k‖)=‖b‖ := by simpa using (lp.hasSum_norm (p := 1) (by simp) b).tsum_eq
    rw [← he]
    exact tsum_comp_le_tsum_of_inj hbZ (fun _ => norm_nonneg _) hj
  have hpoint (m : ℕ+) : (((m:ℕ):ℝ)/(n:ℕ))*‖u n m‖ ≤
      B*(d m+‖κ (j n-j m)‖*‖b (j m)‖+(2/((n:ℕ):ℝ))*‖b (j m)‖) := by
    by_cases hmn : m=n
    · subst m
      have hn : ((n:ℕ):ℝ) ≠ 0 := by exact_mod_cast n.ne_zero
      rw [div_self hn]
      have hnn := hu n n
      rw [if_pos (show n=n from rfl),mul_one] at hnn
      have hdv : d n=‖b (j n)‖ := by simp only [d,if_pos rfl]
      rw [hdv,one_mul,hb]
      apply hnn.trans
      apply mul_le_mul_of_nonneg_left _ hB
      exact le_trans (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_right (by positivity))
    · have hker := positive_weighted_moment_kernel_le n m hmn
      have hum := hu n m
      rw [if_neg hmn] at hum
      have hk : ‖κ (j n-j m)‖=1/|((n:ℕ):ℝ)-(m:ℕ)| := norm_puncturedLattice_positive_difference hp n m hmn
      rw [show d m=0 from if_neg hmn,zero_add,hk,hb]
      calc
        _ ≤ (((m:ℕ):ℝ)/(n:ℕ))*(B*‖g (j m)‖^2*
            (1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ))) :=
          mul_le_mul_of_nonneg_left hum (by positivity)
        _ = (B*‖g (j m)‖^2)*((((m:ℕ):ℝ)/(n:ℕ))*
            (1/|((n:ℕ):ℝ)-(m:ℕ)|+1/((n:ℕ)+(m:ℕ):ℝ))) := by ring
        _ ≤ (B*‖g (j m)‖^2)*(1/|((n:ℕ):ℝ)-(m:ℕ)|+2/((n:ℕ):ℝ)) :=
          mul_le_mul_of_nonneg_left hker (by positivity)
        _ = _ := by ring
  have hsmajor := ((hd.add hcP).add (hbP.mul_left (2/((n:ℕ):ℝ)))).mul_left B
  have hsum := hsw.tsum_le_tsum hpoint hsmajor
  rw [tsum_mul_left,(hd.add hcP).tsum_add (hbP.mul_left (2/((n:ℕ):ℝ))),
    hd.tsum_add hcP,hdSum,tsum_mul_left] at hsum
  have hnκ : ‖κ (j n)‖=1/((n:ℕ):ℝ) := by
    have hn : j n ≠ 0 := by dsimp only [j]; exact_mod_cast n.ne_zero
    rw [show κ (j n)=puncturedLattice p hp (j n) from rfl,puncturedLattice_apply,if_neg hn,norm_inv,
      Complex.norm_intCast]
    simp only [j,Int.cast_natCast,abs_of_nonneg (by positivity : (0:ℝ) ≤ (n:ℕ)),one_div]
  calc
    _ ≤ ‖((n:ℕ):ℂ)⁻¹‖*(∑' m : ℕ+, ‖((m:ℕ):ℂ)*u n m‖) := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsraw) (norm_nonneg _)
    _ = ∑' m : ℕ+, (((m:ℕ):ℝ)/(n:ℕ))*‖u n m‖ := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      simp only [norm_inv,Complex.norm_natCast,norm_mul]
      ring
    _ ≤ B*(‖b (j n)‖+‖convolution (magnitude κ) (magnitude b) (j n)‖+
        (2/((n:ℕ):ℝ))*‖b‖) := hsum.trans (mul_le_mul_of_nonneg_left
          (add_le_add (add_le_add le_rfl hcSum) (mul_le_mul_of_nonneg_left hbSum (by positivity))) hB)
    _ = _ := by rw [norm_squaredGapMomentMajorant_apply]; change _=B*(‖b (j n)‖+_+2*‖b‖*‖κ (j n)‖); rw [hnκ]; ring

end NLS.Coeff
