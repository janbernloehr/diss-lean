import NLS.KdV.HillCharacteristicZeros
import NLS.KdV.HillRealSpectrum

/-! # Supplementary wide-strip Hill estimates

The radius-6n strips retain their existing convention. For n at least two,
the stronger nearest-neighbor lattice gap also permits radius-12n strips.
These supplementary strips overlap on the real axis. The n=1 exclusion
is essential: its radius-12 strip contains the free zero mode.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.KdV

/-- A separate, wider region, used only with n >= 2. -/
def wideHillStrip (n : ℕ) : Set ℂ :=
  {z | |z.re-freeHillValue n| ≤ 12*(n : ℝ)}

theorem freeHill_denominator_lower_wide {n : ℕ} (hn : 2 ≤ n) {z : ℂ}
    (hz : z ∈ wideHillStrip n) {k : ℤ} (hk : k.natAbs ≠ n) :
    |(n : ℝ)^2-(k : ℝ)^2| ≤ ‖z-(freeHillValue k : ℂ)‖ := by
  let d : ℝ := |(n : ℝ)^2-(k : ℝ)^2|
  have hgap : 2*(n : ℝ)-1 ≤ d := two_mul_nat_sub_one_le_abs_sq_sub_sq (by omega) hk
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpi : 9 < Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have he : Real.pi^2*d = |freeHillValue n-freeHillValue k| := by
    dsimp [d, freeHillValue]
    simp only [Int.cast_natCast]
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg Real.pi)]
  have ht : Real.pi^2*d ≤ 12*(n : ℝ)+‖z-(freeHillValue k : ℂ)‖ := by
    rw [he]
    calc
      _ ≤ |freeHillValue n-z.re|+|z.re-freeHillValue k| := by
        simpa using abs_add_le (freeHillValue n-z.re) (z.re-freeHillValue k)
      _ ≤ _ := add_le_add (by simpa only [wideHillStrip, mem_ofPred_eq, abs_sub_comm] using hz)
        (by simpa using Complex.abs_re_le_norm (z-(freeHillValue k : ℂ)))
  have hd : 0 ≤ d := abs_nonneg _
  nlinarith

/-- Eigenvector localization from the denominator bound alone. This uses
the actual Fourier equation and the L2-to-L1 gain, without presupposing a
narrow-strip reduction. -/
theorem hillEigenvector_localization_of_denominator_lower
    (q : Coeff 2) (n : ℕ) (hn : 1 ≤ n) (z : ℂ)
    (hdenom : ∀ k : ℤ, k.natAbs ≠ n → |(n : ℝ)^2-(k : ℝ)^2| ≤
      ‖z-(freeHillValue k : ℂ)‖)
    (hcut : 8*‖q‖ ≤ (n : ℝ))
    (f : HillSobolevDomain) (hf : f ≠ 0)
    (he : hillOperator q f = z • hillDomainToL2 f) :
    ‖z-(freeHillValue n : ℂ)‖ ≤ 4*‖q‖ := by
  let a := hillDomainToL1 f
  let v := Coeff.convolution q a
  let s := hillReciprocalHilbertSymbolOfLower n hn z hdenom
  let b := Coeff.holderProduct (q := 1) v s
  let m : Coeff 1 := a n • lp.single 1 (n : ℤ) (1 : ℂ) +
    a (-(n : ℤ)) • lp.single 1 (-(n : ℤ)) (1 : ℂ)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hcoeff (k : ℤ) : v k = (z-(freeHillValue k : ℂ))*a k := by
    have h := congrArg (fun u : Coeff 2 => u k) he
    simp only [hillOperator_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      hillDomainToL2_apply] at h
    have hvk : v k = ∑' j : ℤ, q (k-j)*f.val j := by
      simp only [v, Coeff.convolution_apply, a, hillDomainToL1_apply]
    rw [← hvk] at h
    simpa only [a, hillDomainToL1_apply] using
      (show v k = (z-(freeHillValue k : ℂ))*f.val k by linear_combination h)
  have hfree (k : ℤ) (hk : k.natAbs ≠ n) : z-(freeHillValue k : ℂ) ≠ 0 := by
    apply norm_pos_iff.mp
    exact hnpos.trans_le ((nat_le_abs_sq_sub_sq hn hk).trans (hdenom k hk))
  have hsplit : a = m+b := by
    ext k
    simp only [m, b, s, lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, lp.single_apply, Coeff.holderProduct_apply,
      hillReciprocalHilbertSymbolOfLower_apply]
    by_cases hp : k = (n : ℤ)
    · subst k
      simp [show (n : ℤ) ≠ -(n : ℤ) by omega]
    by_cases hm : k = -(n : ℤ)
    · subst k
      simp [show -(n : ℤ) ≠ (n : ℤ) by omega]
    have hk : k.natAbs ≠ n := by
      intro hk
      have he' : k = (n : ℤ) ∨ k = -(n : ℤ) :=
        (Int.natAbs_eq_natAbs_iff).mp (by simpa using hk)
      exact he'.elim hp hm
    simp only [Pi.single_eq_of_ne hp, Pi.single_eq_of_ne hm, mul_zero, zero_add,
      if_neg hk, hcoeff]
    field_simp [hfree k hk]
  have hA : 0 < ‖a‖ := by
    apply norm_pos_iff.mpr
    intro hz
    apply hf
    apply Subtype.ext
    funext k
    have h := congrArg (fun u : Coeff 1 => u k) hz
    simpa only [a, hillDomainToL1_apply, lp.coeFn_zero, Pi.zero_apply, WeightedCoeff.zero_val] using h
  have hv : ‖v‖ ≤ ‖q‖*‖a‖ := Coeff.norm_convolution_le q a
  have hb : ‖b‖ ≤ (4/(n : ℝ))*‖v‖ := by
    exact (Coeff.norm_holderProduct_le v s).trans
      (by nlinarith [norm_hillReciprocalHilbertSymbolOfLower_le n hn z hdenom, norm_nonneg v])
  have htail : (4/(n : ℝ))*‖q‖ ≤ 1/2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hnpos]
    linarith
  have hmass : ‖a‖/2 ≤ ‖m‖ := by
    have h := norm_add_le m b
    rw [← hsplit] at h
    have hb' := hb.trans (mul_le_mul_of_nonneg_left hv (by positivity : 0 ≤ 4/(n : ℝ)))
    have ht := mul_le_mul_of_nonneg_right htail (norm_nonneg a)
    nlinarith
  have hmnorm : ‖m‖ ≤ ‖a n‖+‖a (-(n : ℤ))‖ := by
    exact (norm_add_le _ _).trans_eq (by
      simp only [norm_smul, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 1), norm_one, mul_one])
  have hmD : ‖z-(freeHillValue n : ℂ)‖*‖m‖ ≤ 2*‖q‖*‖a‖ := by
    have hp := congrArg norm (hcoeff (n : ℤ))
    have hm := congrArg norm (hcoeff (-(n : ℤ)))
    rw [norm_mul] at hp
    rw [freeHillValue_neg, norm_mul] at hm
    have hvp := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) v (n : ℤ)
    have hvm := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) v (-(n : ℤ))
    have hbound := mul_le_mul_of_nonneg_left hmnorm (norm_nonneg (z-(freeHillValue n : ℂ)))
    nlinarith
  have h := (mul_le_mul_of_nonneg_left hmass
    (norm_nonneg (z-(freeHillValue n : ℂ)))).trans hmD
  nlinarith

theorem hillEigenvector_localization_wide (q : Coeff 2) (n : ℕ) (hn : 2 ≤ n)
    (z : ℂ) (hz : z ∈ wideHillStrip n) (hcut : 8*‖q‖ ≤ (n : ℝ))
    (f : HillSobolevDomain) (hf : f ≠ 0)
    (he : hillOperator q f = z • hillDomainToL2 f) :
    ‖z-(freeHillValue n : ℂ)‖ ≤ 4*‖q‖ :=
  hillEigenvector_localization_of_denominator_lower q n (by omega) z
    (fun _ hk => freeHill_denominator_lower_wide hn hz hk) hcut f hf he

/-- The supplementary wide strips cover the high real half-line.
This is a geometric covering statement, independent of the potential. -/
theorem exists_wideHillStrip_of_ge (N : ℕ) (hN : 2 ≤ N) (lambda : ℝ)
    (hlambda : freeHillValue N ≤ lambda) :
    ∃ n : ℕ, N ≤ n ∧ (lambda : ℂ) ∈ wideHillStrip n := by
  have hl0 : 0 ≤ lambda := (by unfold freeHillValue; positivity : 0 ≤ freeHillValue N).trans hlambda
  let t := Real.sqrt lambda/Real.pi
  let m := Nat.floor t
  have ht0 : 0 ≤ t := div_nonneg (Real.sqrt_nonneg _) Real.pi_pos.le
  have hNt : (N : ℝ) ≤ t := by
    apply (le_div_iff₀ Real.pi_pos).mpr
    have hs : ((N : ℝ)*Real.pi)^2 ≤ (Real.sqrt lambda)^2 := by
      rw [Real.sq_sqrt hl0]
      simpa only [freeHillValue, Int.cast_natCast, mul_pow, mul_comm] using hlambda
    exact (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp hs
  have hNm : N ≤ m := Nat.le_floor hNt
  have hlo : freeHillValue m ≤ lambda := by
    have h := (le_div_iff₀ Real.pi_pos).mp (Nat.floor_le ht0)
    have hs := (sq_le_sq₀ (by positivity : 0 ≤ (m : ℝ)*Real.pi)
      (Real.sqrt_nonneg lambda)).mpr h
    rw [Real.sq_sqrt hl0] at hs
    simpa only [freeHillValue, Int.cast_natCast, mul_pow, mul_comm] using hs
  have hhi : lambda < freeHillValue (m+1 : ℕ) := by
    have h := (div_lt_iff₀ Real.pi_pos).mp (Nat.lt_floor_add_one t)
    have hs := (sq_lt_sq₀ (Real.sqrt_nonneg lambda)
      (by positivity : 0 ≤ ((m : ℝ)+1)*Real.pi)).mpr h
    rw [Real.sq_sqrt hl0] at hs
    simpa only [freeHillValue, Int.cast_add, Int.cast_natCast, Int.cast_one,
      Nat.cast_add, Nat.cast_one, mul_pow, mul_comm] using hs
  have hstep : freeHillValue (m+1 : ℕ)-freeHillValue m ≤
      12*(m : ℝ)+12*((m+1 : ℕ) : ℝ) := by
    have hpi : Real.pi^2 ≤ 12 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
    have hp := mul_nonneg (sub_nonneg.mpr hpi) (by positivity : 0 ≤ 2*(m : ℝ)+1)
    dsimp [freeHillValue]
    push_cast
    nlinarith
  by_cases hm : lambda ≤ freeHillValue m+12*(m : ℝ)
  · refine ⟨m,hNm,?_⟩
    change |lambda-freeHillValue m| ≤ 12*(m : ℝ)
    rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
    linarith
  · refine ⟨m+1,by omega,?_⟩
    change |lambda-freeHillValue (m+1 : ℕ)| ≤ 12*((m+1 : ℕ) : ℝ)
    rw [abs_of_nonpos (sub_nonpos.mpr hhi.le)]
    linarith

theorem exists_wideHillStrip_of_ge_lower_edge (N : ℕ) (hN : 2 ≤ N) (lambda : ℝ)
    (hlambda : freeHillValue N-12*(N : ℝ) ≤ lambda) :
    ∃ n : ℕ, N ≤ n ∧ (lambda : ℂ) ∈ wideHillStrip n := by
  by_cases h : freeHillValue N ≤ lambda
  · exact exists_wideHillStrip_of_ge N hN lambda h
  · refine ⟨N,le_rfl,?_⟩
    change |lambda-freeHillValue N| ≤ 12*(N : ℝ)
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- Every sufficiently high real Hill eigenvalue belongs to an original
narrow strip and obeys the same radius-4||q|| localization. -/
theorem hillEigenvalue_real_high_cover (q : Coeff 2) (N : ℕ) (hN : 2 ≤ N)
    (hcut : 8*‖q‖ ≤ (N : ℝ)) (lambda : ℝ)
    (hlambda : freeHillValue N-12*(N : ℝ) ≤ lambda)
    (f : HillSobolevDomain) (hf : f ≠ 0)
    (he : hillOperator q f = (lambda : ℂ) • hillDomainToL2 f) :
    ∃ n : ℕ, N ≤ n ∧ ‖(lambda : ℂ)-(freeHillValue n : ℂ)‖ ≤ 4*‖q‖ ∧
      (lambda : ℂ) ∈ reducedHillStrip n := by
  obtain ⟨n,hn,hz⟩ := exists_wideHillStrip_of_ge_lower_edge N hN lambda hlambda
  have hc : 8*‖q‖ ≤ (n : ℝ) := hcut.trans (by exact_mod_cast hn)
  have hloc := hillEigenvector_localization_wide q n (hN.trans hn) lambda hz hc f hf he
  refine ⟨n,hn,hloc,?_⟩
  change |lambda-freeHillValue n| ≤ 6*(n : ℝ)
  have hr : |lambda-freeHillValue n| ≤ ‖(lambda : ℂ)-(freeHillValue n : ℂ)‖ := by
    simpa using Complex.abs_re_le_norm ((lambda : ℂ)-(freeHillValue n : ℂ))
  linarith [norm_nonneg q]

/-- For a real period-one L2 potential there are no extra high-energy
characteristic roots between the original narrow strips. -/
theorem hillL2Radicand_real_high_cover
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ))
    (lambda : ℂ) (hlambda : freeHillValue N-12*(N : ℝ) ≤ lambda.re)
    (hd : hillL2Radicand (SpectralWeight.one.toCoeff q) lambda = 0) :
    ∃ n : ℕ, N ≤ n ∧ ‖lambda-(freeHillValue n : ℂ)‖ ≤ 4*‖q‖ ∧
      lambda ∈ reducedHillStrip n := by
  obtain ⟨f,hf,he⟩ := (hill_eigenvector_iff_l2Discriminant q hq lambda).mpr (sub_eq_zero.mp hd)
  have him := hillL2Discriminant_root_im_zero q hq hreal lambda (sub_eq_zero.mp hd)
  have hl : (lambda.re : ℂ) = lambda := by apply Complex.ext <;> simp [him]
  have hc : 8*‖SpectralWeight.one.toCoeff q‖ ≤ (N : ℝ) := by
    linarith [SpectralWeight.norm_toCoeff_le SpectralWeight.one q]
  have he' : hillOperator (SpectralWeight.one.toCoeff q) f =
      (lambda.re : ℂ) • hillDomainToL2 f := by rwa [hl]
  obtain ⟨n,hn,hloc,hz⟩ := hillEigenvalue_real_high_cover
    (SpectralWeight.one.toCoeff q) N hN hc lambda.re hlambda f hf he'
  rw [hl] at hloc hz
  exact ⟨n,hn,hloc.trans (by linarith [SpectralWeight.norm_toCoeff_le SpectralWeight.one q]),hz⟩

/-- The same reciprocal estimate also controls the left half-plane.
This coarse quadratic bound requires no reality or mean-zero assumption. -/
theorem hillEigenvalue_re_lower_bound (q : Coeff 2) (N : ℕ) (hN : 1 ≤ N)
    (hcut : 8*‖q‖ ≤ (N : ℝ)) (z : ℂ)
    (f : HillSobolevDomain) (hf : f ≠ 0)
    (he : hillOperator q f = z • hillDomainToL2 f) : -(N : ℝ)^2 < z.re := by
  by_contra! hz
  have hpi : 1 ≤ Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hden (k : ℤ) : |(N : ℝ)^2-(k : ℝ)^2| ≤ ‖z-(freeHillValue k : ℂ)‖ := by
    have hk : (k : ℝ)^2 ≤ freeHillValue k := by
      dsimp [freeHillValue]
      nlinarith [mul_le_mul_of_nonneg_right hpi (sq_nonneg (k : ℝ))]
    calc
      _ ≤ (N : ℝ)^2+(k : ℝ)^2 := by
        exact abs_le.mpr ⟨by nlinarith [sq_nonneg (N : ℝ)], by nlinarith [sq_nonneg (k : ℝ)]⟩
      _ ≤ freeHillValue k-z.re := by linarith
      _ = |z.re-freeHillValue k| := by
        rw [abs_of_nonpos (by linarith [sq_nonneg (N : ℝ), sq_nonneg (k : ℝ)])]
        ring
      _ ≤ _ := by simpa using Complex.abs_re_le_norm (z-(freeHillValue k : ℂ))
  have hloc := hillEigenvector_localization_of_denominator_lower q N hN z
    (fun k _ => hden k) hcut f hf he
  have hr : |z.re-freeHillValue N| ≤ ‖z-(freeHillValue N : ℂ)‖ := by
    simpa using Complex.abs_re_le_norm (z-(freeHillValue N : ℂ))
  have hNN : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hfree : 0 ≤ freeHillValue N := by unfold freeHillValue; positivity
  rw [abs_of_nonpos (by linarith [sq_nonneg (N : ℝ)])] at hr
  nlinarith

theorem hillL2Radicand_re_lower_bound
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (N : ℕ) (hN : 1 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ)) (z : ℂ)
    (hd : hillL2Radicand (SpectralWeight.one.toCoeff q) z = 0) : -(N : ℝ)^2 < z.re := by
  obtain ⟨f,hf,he⟩ := (hill_eigenvector_iff_l2Discriminant q hq z).mpr (sub_eq_zero.mp hd)
  exact hillEigenvalue_re_lower_bound _ N hN
    (by linarith [SpectralWeight.norm_toCoeff_le SpectralWeight.one q]) z f hf he

/-- A physical characteristic root cannot belong to two distinct checked
high strips. The assertion also holds for complex potentials. -/
theorem hillL2Radicand_high_index_unique
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (hcn : 8*‖q‖ ≤ (n : ℝ)) (hcm : 8*‖q‖ ≤ (m : ℝ))
    (z : ℂ) (hzn : z ∈ reducedHillStrip n) (hzm : z ∈ reducedHillStrip m)
    (hd : hillL2Radicand (SpectralWeight.one.toCoeff q) z = 0) : n = m := by
  by_contra hne
  have hsep := freeHill_denominator_ge_index hn hzn
    (k := (m : ℤ)) (by simpa using Ne.symm hne)
  have hloc := hillL2Radicand_zero_localization q hq m hm z hzm hcm hd
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  nlinarith

/-- Global real high-tail coverage and uniqueness of its free lattice
index. This closes the real spectral gaps between the narrow strips. -/
theorem hillL2Radicand_real_high_index
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ))
    (z : ℂ) (hz : freeHillValue N-12*(N : ℝ) ≤ z.re)
    (hd : hillL2Radicand (SpectralWeight.one.toCoeff q) z = 0) :
    ∃! n : ℕ, N ≤ n ∧ z ∈ reducedHillStrip n := by
  obtain ⟨n,hn,_,hzn⟩ := hillL2Radicand_real_high_cover q hq hreal N hN hcut z hz hd
  refine ⟨n,⟨hn,hzn⟩,?_⟩
  rintro m ⟨hm,hzm⟩
  exact hillL2Radicand_high_index_unique q hq m n (by omega) (by omega)
    (hcut.trans (by exact_mod_cast hm)) (hcut.trans (by exact_mod_cast hn)) z hzm hzn hd

/-- The lower edge of the first wide strip is a zero-free vertical line,
uniformly on the complex potential ball with the stated cutoff. -/
theorem hillL2Radicand_ne_zero_on_central_separator
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ))
    (z : ℂ) (hz : z.re = freeHillValue N-12*(N : ℝ)) :
    hillL2Radicand (SpectralWeight.one.toCoeff q) z ≠ 0 := by
  intro hd
  obtain ⟨f,hf,he⟩ := (hill_eigenvector_iff_l2Discriminant q hq z).mpr (sub_eq_zero.mp hd)
  have hzn : z ∈ wideHillStrip N := by
    change |z.re-freeHillValue N| ≤ 12*(N : ℝ)
    rw [hz]
    simp
  have hc : 8*‖SpectralWeight.one.toCoeff q‖ ≤ (N : ℝ) := by
    linarith [SpectralWeight.norm_toCoeff_le SpectralWeight.one q]
  have hloc := hillEigenvector_localization_wide _ N hN z hzn hc f hf he
  have hr : |z.re-freeHillValue N| ≤ ‖z-(freeHillValue N : ℂ)‖ := by
    simpa using Complex.abs_re_le_norm (z-(freeHillValue N : ℂ))
  rw [hz] at hr
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have habs : |freeHillValue N-12*(N : ℝ)-freeHillValue N| = 12*(N : ℝ) := by
    rw [show freeHillValue N-12*(N : ℝ)-freeHillValue N = -12*(N : ℝ) by ring]
    simp
  rw [habs] at hr
  nlinarith

/-- Every actual characteristic root for a real potential lies either in
the explicit bounded central interval or in a unique high strip. -/
theorem hillL2Radicand_real_central_or_high
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hreal : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (N : ℕ) (hN : 2 ≤ N) (hcut : 8*‖q‖ ≤ (N : ℝ))
    (z : ℂ) (hd : hillL2Radicand (SpectralWeight.one.toCoeff q) z = 0) :
    z.im = 0 ∧ (z.re ∈ Ioo (-(N : ℝ)^2) (freeHillValue N-12*(N : ℝ)) ∨
      ∃! n : ℕ, N ≤ n ∧ z ∈ reducedHillStrip n) := by
  refine ⟨hillL2Discriminant_root_im_zero q hq hreal z (sub_eq_zero.mp hd),?_⟩
  by_cases hz : freeHillValue N-12*(N : ℝ) ≤ z.re
  · exact Or.inr (hillL2Radicand_real_high_index q hq hreal N hN hcut z hz hd)
  · exact Or.inl ⟨hillL2Radicand_re_lower_bound q hq N (by omega) hcut z hd, by linarith⟩

end NLS.KdV
