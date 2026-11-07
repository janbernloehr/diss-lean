import NLS.SequenceSpaces.PeriodOneMiuraShift
import NLS.SequenceSpaces.SobolevDerivative
import NLS.SequenceSpaces.HolderEmbedding
import NLS.SequenceSpaces.BoundedScalarProducts

/-!
# Exact finite-p regularity of rough Miura lifts

An L2 product has bounded Fourier coefficients. Above the strict negative
weight summability threshold this quadratic term belongs to the requested
finite-p space. The Miura equation then gains exactly one derivative in
both directions, with no endpoint membership assumed in advance.
-/
noncomputable section
open Complex
open scoped ENNReal
namespace NLS
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The Fourier product of two L2 inputs has every negative finite-p
Sobolev weight strictly beyond its summability threshold. -/
theorem memlp_negative_sobolev_l2_product (r : ℝ) (hp : p ≠ ⊤)
    (hrp : 1 < r*p.toReal) (u v : Coeff 2) :
    Memℓp (fun n : ℤ => (Weight.sobolev (-r) n : ℂ)*
      (∑' j : ℤ, u (n-j)*v j)) p := by
  have hpR : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hp
  have hw : Memℓp (fun n : ℤ => (Weight.sobolev (-r) n : ℂ)) p := by
    have he : (fun n : ℤ => (Weight.sobolev (-r) n : ℂ)) =
        fun n => (Weight.sobolev r n : ℂ)⁻¹ := by
      funext n
      simp only [Weight.sobolev_apply,
        Real.rpow_neg (show 0 ≤ 1+|(n : ℝ)| by positivity),Complex.ofReal_inv]
    rw [he]
    exact Weight.inverse_sobolev_memlp hpR hrp
  let b := Coeff.youngConvolution youngRelation_two_two_top u v
  have hb := memlp_smul_of_bounded_vector
    (fun n : ℤ => (Weight.sobolev (-r) n : ℂ)) (fun n : ℤ => b n) hw ‖b‖
      (fun n => lp.norm_apply_le_norm (by simp) b n)
  exact hb

/-- At the strict negative-weight threshold, a rough Miura image has
regularity -r in finite p exactly when its L2 lift has regularity 1-r.
The exponent condition p>=2 supplies the lower-order term of the lift. -/
theorem periodOneMiura_memlp_iff (r : ℝ) (hp : p ≠ ⊤) (hp2 : 2 ≤ p)
    (hrp : 1 < r*p.toReal) (u : Coeff 2) :
    Memℓp (fun n : ℤ => (Weight.sobolev (-r) n : ℂ)*(periodOneMiura u).val n) p ↔
      Memℓp (fun n : ℤ => (Weight.sobolev (1-r) n : ℂ)*u n) p := by
  have hpR : 0 < p.toReal := ENNReal.toReal_pos (by
    have : (0 : ℝ≥0∞) < 2 := by norm_num
    exact ne_of_gt (this.trans_le hp2)) hp
  have hr : 0 < r := by nlinarith
  have hb := memlp_negative_sobolev_l2_product r hp hrp u u
  have hu : Memℓp (fun n : ℤ => (Weight.sobolev (-r) n : ℂ)*u n) p := by
    apply ((lp.memℓp u).of_exponent_ge hp2).mono'
    intro n
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos ((Weight.sobolev (-r)).positive n)]
    have hw : Weight.sobolev (-r) n ≤ 1 := by
      simpa only [Weight.sobolev_zero_apply] using Weight.sobolev_mono (by linarith : -r ≤ 0) n
    exact mul_le_of_le_one_left (norm_nonneg _) hw
  constructor
  · intro hq
    have hd : Memℓp (fun n : ℤ => (Weight.sobolev (-r) n : ℂ)*
        (I*(Real.pi : ℂ)*n*u n)) p := by
      have he : (fun n : ℤ => (Weight.sobolev (-r) n : ℂ)*(I*(Real.pi : ℂ)*n*u n)) =
          fun n => (1/2 : ℂ)*((Weight.sobolev (-r) n : ℂ)*(periodOneMiura u).val n-
            (Weight.sobolev (-r) n : ℂ)*(∑' j : ℤ, u (n-j)*u j)) := by
        funext n
        rw [periodOneMiura_apply]
        ring
      rw [he]
      exact (hq.sub hb).const_mul (1/2 : ℂ)
    simpa only [show -r+1 = 1-r by ring] using
      WeightedCoeff.memlp_sobolev_succ_of_derivative (-r) hu hd
  · intro hreg
    let a : WeightedCoeff (Weight.sobolev (-r+1)) p :=
      ⟨u,by
        change Memℓp (fun n : ℤ => (Weight.sobolev (-r+1) n : ℂ)*u n) p
        simpa only [show -r+1 = 1-r by ring] using hreg⟩
    have hd := (WeightedCoeff.sobolevDerivative (-r) a).property
    have he : (fun n : ℤ => (Weight.sobolev (-r) n : ℂ)*(periodOneMiura u).val n) =
        fun n => (2 : ℂ)*((Weight.sobolev (-r) n : ℂ)*(I*(Real.pi : ℂ)*n*u n))+
          (Weight.sobolev (-r) n : ℂ)*(∑' j : ℤ, u (n-j)*u j) := by
      funext n
      rw [periodOneMiura_apply]
      ring
    rw [he]
    exact (hd.const_mul (2 : ℂ)).add hb

/-- A constant energy translation does not change the exact finite-p
Miura regularity criterion for the identical H-minus-one coefficients. -/
theorem periodOneMiura_shift_memlp_iff (r : ℝ) (hp : p ≠ ⊤) (hp2 : 2 ≤ p)
    (hrp : 1 < r*p.toReal) (u : Coeff 2) (q : PeriodOneHminusOne) (c : ℂ)
    (himage : periodOneMiura u = q+periodOneL2Inclusion (lp.single 2 0 c)) :
    Memℓp (fun n : ℤ => (Weight.sobolev (-r) n : ℂ)*q.val n) p ↔
      Memℓp (fun n : ℤ => (Weight.sobolev (1-r) n : ℂ)*u n) p := by
  have hc : Memℓp (fun n : ℤ => (Weight.sobolev (-r) n : ℂ)*
      (periodOneL2Inclusion (lp.single 2 0 c)).val n) p := by
    convert lp.memℓp (lp.single p (0:ℤ) c : Coeff p) using 1
    funext n
    by_cases hn : n = 0
    · subst n
      simp only [periodOneL2Inclusion_apply,lp.single_apply,Pi.single_apply,if_true,
        Weight.sobolev_apply,Int.cast_zero,abs_zero,add_zero,Real.one_rpow,ofReal_one,one_mul]
    · simp only [periodOneL2Inclusion_apply,lp.single_apply,Pi.single_apply,if_neg hn,mul_zero]
  have he : (fun n : ℤ => (Weight.sobolev (-r) n : ℂ)*(periodOneMiura u).val n) =
      (fun n : ℤ => (Weight.sobolev (-r) n : ℂ)*q.val n)+
        (fun n : ℤ => (Weight.sobolev (-r) n : ℂ)*
          (periodOneL2Inclusion (lp.single 2 0 c)).val n) := by
    funext n
    rw [himage]
    change (Weight.sobolev (-r) n : ℂ)*(q.val n+
      (periodOneL2Inclusion (lp.single 2 0 c)).val n) = _
    exact mul_add _ _ _
  rw [← periodOneMiura_memlp_iff r hp hp2 hrp u,he]
  constructor
  · exact fun hq => hq.add hc
  · intro hsum
    convert hsum.sub hc using 1
    funext n
    simp only [Pi.add_apply,Pi.sub_apply,add_sub_cancel_right]

end NLS
