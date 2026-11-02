import NLS.ZakharovShabat.SourceStandardRootNorm
import NLS.ZakharovShabat.SourceH1CentralProductBound

/-! The enclosing standard-root ratio in the complex H1 argument of Section 28. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Bounds on both endpoint distances bound the normalized root even at
the midpoint, where its defining expression vanishes. -/
theorem section28_standardRoot_norm_upper
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m : ℤ) (z : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hl : ‖canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z‖ ≤ R)
    (hr : ‖canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z‖ ≤ R) :
    ‖sourceStandardRoot hp hp1 ψ m z‖ ≤ R := by
  by_cases hz : z = canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m
  · simp only [sourceStandardRoot, normalizedStandardRoot, hz, sub_self, zero_mul, norm_zero]
    exact hR
  · have he := congrArg norm (sourceStandardRoot_sq_of_ne_midpoint hp hp1 ψ m z hz)
    simp only [norm_pow, norm_mul] at he
    have hb := mul_le_mul hl hr (norm_nonneg _) hR
    nlinarith [norm_nonneg (sourceStandardRoot hp hp1 ψ m z)]

/-- A vertical half-plane containing both endpoints gives a root lower
bound at every spectral point strictly to its right. -/
theorem section28_standardRoot_norm_lower_of_re
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m : ℤ) (z : ℂ) (A : ℝ)
    (hl : (canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m).re ≤ A)
    (hr : (canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m).re ≤ A)
    (hz : A < z.re) :
    z.re-A ≤ ‖sourceStandardRoot hp hp1 ψ m z‖ := by
  have hm : (canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m).re ≤ A := by
    simp only [canonicalPeriodicMidpoint, div_ofNat_re, add_re]
    linarith
  have hne : z ≠ canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    intro he
    rw [← he] at hm
    exact (not_le_of_gt hz) hm
  have hleft : z.re-A ≤ ‖canonicalPeriodicLeft hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z‖ := by
    have h := Complex.re_le_norm (z-canonicalPeriodicLeft hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    rw [sub_re, norm_sub_rev] at h
    linarith
  have hright : z.re-A ≤ ‖canonicalPeriodicRight hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m-z‖ := by
    have h := Complex.re_le_norm (z-canonicalPeriodicRight hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m)
    rw [sub_re, norm_sub_rev] at h
    linarith
  have he := congrArg norm (sourceStandardRoot_sq_of_ne_midpoint hp hp1 ψ m z hne)
  simp only [norm_pow, norm_mul] at he
  have hb := mul_le_mul hleft hright (sub_nonneg.mpr hz.le) (norm_nonneg _)
  nlinarith [norm_nonneg (sourceStandardRoot hp hp1 ψ m z)]

/-- Two localization discs centered on the real line give an exact
upper distance bound, without a reality assumption on either point. -/
theorem section28_localized_distance_upper (u z : ℂ) (x y r : ℝ)
    (hyx : y ≤ x) (hu : ‖u-(y : ℂ)‖ ≤ r) (hz : ‖z-(x : ℂ)‖ ≤ r) :
    ‖u-z‖ ≤ x-y+2*r := by
  have hmid : ‖(y : ℂ)-(x : ℂ)‖ = x-y := by
    rw [← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hyx)]
    ring
  calc
    ‖u-z‖ ≤ ‖u-(y : ℂ)‖+‖(y : ℂ)-z‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ r+(‖(y : ℂ)-(x : ℂ)‖+‖(x : ℂ)-z‖) :=
      add_le_add hu (norm_sub_le_norm_sub_add_norm_sub _ _ _)
    _ ≤ r+(x-y+r) := by rw [hmid, norm_sub_rev (x : ℂ) z]; gcongr
    _ = x-y+2*r := by ring

/-- The printed enclosing-root ratio holds for actual complex H1 sources
on the full positive exterior gap, including the boundary index n=N. -/
theorem section28_complex_enclosing_root_ratio
    (ψ : CoeffPair 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ)
    (N : ℕ) (hNpos : 1 ≤ N) (hN : 8*‖φ‖^2 ≤ 1+(N : ℝ))
    (n : ℤ) (hn : (N : ℤ) ≤ n) (z : ℂ)
    (hz : z ∈ sourcePeriodicSegment (by simp) (by norm_num) ψ n) :
    ‖sourceStandardRoot (by simp) (by norm_num) ψ (-(N : ℤ)) z /
      sourceStandardRoot (by simp) (by norm_num) ψ ((N : ℤ)-1) z‖ ≤
      ((n : ℝ)+N+2/5)/((n : ℝ)-N+3/10) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈ pairParitySubspace 0 :=
    hφ ▸ periodOnePotential_mem ψ
  have hncut : 8*‖φ‖^2 ≤ 1+|(n : ℝ)| := by rw [abs_of_nonneg hn0]; linarith
  have hloc := sourceH1_gap_point_norm_localization ψ φ hφ n hncut z hz
  have hzr : Real.pi*(n : ℝ)-Real.pi/5 ≤ z.re := by
    have h := (Complex.abs_re_le_norm (z-(Real.pi : ℂ)*n)).trans hloc
    simp only [sub_re, mul_re, ofReal_re, intCast_re, ofReal_im, zero_mul, sub_zero] at h
    linarith [(abs_le.mp h).1]
  have hleft := (H1_periodicSpectrum_uniform_localization φ heven).1 (-(N : ℤ)) (by
    simpa only [Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (show (0 : ℝ) ≤ N from Nat.cast_nonneg N)] using hN)
  simp only [hφ] at hleft
  let U : ℝ := ((n : ℝ)+N+2/5)*Real.pi
  let D : ℝ := ((n : ℝ)-N+3/10)*Real.pi
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hD : 0 < D := by dsimp [D]; apply mul_pos _ Real.pi_pos; linarith
  have hupper (u : ℂ) (hu : ‖u-(Real.pi : ℂ)*(-(N : ℤ))‖ ≤ Real.pi/5) : ‖u-z‖ ≤ U := by
    have hu' : ‖u-((Real.pi*(-(N : ℝ)) : ℝ) : ℂ)‖ ≤ Real.pi/5 := by
      simpa only [ofReal_mul, ofReal_neg, ofReal_natCast, Int.cast_neg, Int.cast_natCast] using hu
    have hz' : ‖z-((Real.pi*(n : ℝ) : ℝ) : ℂ)‖ ≤ Real.pi/5 := by
      simpa only [ofReal_mul, ofReal_intCast] using hloc
    have hh := section28_localized_distance_upper u z (Real.pi*n) (Real.pi*(-(N : ℝ)))
      (Real.pi/5) (by nlinarith [Real.pi_pos]) hu' hz'
    exact hh.trans_eq (by dsimp [U]; ring)
  have hnum : ‖sourceStandardRoot (by simp) (by norm_num) ψ (-(N : ℤ)) z‖ ≤ U :=
    section28_standardRoot_norm_upper (by simp) (by norm_num) ψ _ z U hU
      (hupper _ (by simpa only [Int.cast_neg, Int.cast_natCast] using hleft.1.trans hleft.2.2.le))
      (hupper _ (by simpa only [Int.cast_neg, Int.cast_natCast] using hleft.2.1.trans hleft.2.2.le))
  have hcentral := H1_canonicalEndpoints_cutoff_central_re φ heven N hN ((N : ℤ)-1) (by omega)
  simp only [hφ] at hcentral
  have hden : D ≤ ‖sourceStandardRoot (by simp) (by norm_num) ψ ((N : ℤ)-1) z‖ := by
    have hh := section28_standardRoot_norm_lower_of_re (by simp) (by norm_num) ψ ((N : ℤ)-1) z
      (((N : ℝ)-1/2)*Real.pi) (le_of_abs_le hcentral.1) (le_of_abs_le hcentral.2)
      (by nlinarith [Real.pi_pos])
    apply le_trans _ hh
    dsimp [D]
    nlinarith
  have hratio : U/D = ((n : ℝ)+N+2/5)/((n : ℝ)-N+3/10) := by
    dsimp [U, D]
    exact mul_div_mul_right _ _ Real.pi_ne_zero
  rw [norm_div, ← hratio]
  apply (div_le_iff₀ (hD.trans_le hden)).mpr
  calc
    _ ≤ U := hnum
    _ = U/D*D := (div_mul_cancel₀ U hD.ne').symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (div_nonneg hU hD.le)

/-- A vertical strip containing both endpoints bounds the root from below
on either exterior side, with no reflection of the source potential. -/
theorem section28_standardRoot_norm_lower_of_abs_re
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (m : ℤ) (z : ℂ) (A : ℝ)
    (hl : |(canonicalPeriodicLeft hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m).re| ≤ A)
    (hr : |(canonicalPeriodicRight hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) m).re| ≤ A)
    (hz : A < |z.re|) :
    |z.re|-A ≤ ‖sourceStandardRoot hp hp1 ψ m z‖ := by
  have hm : |(canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m).re| ≤ A := by
    simp only [canonicalPeriodicMidpoint, div_ofNat_re, add_re]
    apply abs_le.mpr
    constructor <;> linarith [(abs_le.mp hl).1, (abs_le.mp hl).2,
      (abs_le.mp hr).1, (abs_le.mp hr).2]
  have hne : z ≠ canonicalPeriodicMidpoint hp hp1
      (periodOnePotential ψ) (periodOnePotential_mem ψ) m := by
    intro he
    rw [← he] at hm
    exact (not_le_of_gt hz) hm
  have hb (u : ℂ) (hu : |u.re| ≤ A) : |z.re|-A ≤ ‖u-z‖ := by
    have h := Complex.abs_re_le_norm (u-z)
    rw [sub_re, abs_sub_comm] at h
    linarith [abs_sub_abs_le_abs_sub z.re u.re]
  have he := congrArg norm (sourceStandardRoot_sq_of_ne_midpoint hp hp1 ψ m z hne)
  simp only [norm_pow, norm_mul] at he
  have hprod := mul_le_mul (hb _ hl) (hb _ hr) (sub_nonneg.mpr hz.le) (norm_nonneg _)
  nlinarith [norm_nonneg (sourceStandardRoot hp hp1 ψ m z)]

/-- Either boundary standard root divided by any central standard root
has the same complex H1 bound on both signed exterior gaps. -/
theorem section28_complex_enclosing_root_ratio_signed
    (ψ : CoeffPair 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N : ℝ))
    (m k n : ℤ) (hm : m.natAbs = N) (hk : k.natAbs < N) (hn : N ≤ n.natAbs)
    (z : ℂ) (hz : z ∈ sourcePeriodicSegment (by simp) (by norm_num) ψ n) :
    ‖sourceStandardRoot (by simp) (by norm_num) ψ m z /
      sourceStandardRoot (by simp) (by norm_num) ψ k z‖ ≤
      (|(n : ℝ)|+N+2/5)/(|(n : ℝ)|-N+3/10) := by
  have hnN : (N : ℝ) ≤ |(n : ℝ)| := by
    have h : (N : ℝ) ≤ (n.natAbs : ℝ) := by exact_mod_cast hn
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  have hmN : |(m : ℝ)| = N := by
    have h : (m.natAbs : ℝ) = (N : ℝ) := by exact_mod_cast hm
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  have heven : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ ∈ pairParitySubspace 0 :=
    hφ ▸ periodOnePotential_mem ψ
  have hncut : 8*‖φ‖^2 ≤ 1+|(n : ℝ)| := by linarith
  have hloc := sourceH1_gap_point_norm_localization ψ φ hφ n hncut z hz
  have hzr := localized_point_abs_re_lower z n hloc
  have hboundary := (H1_periodicSpectrum_uniform_localization φ heven).1 m (by rwa [hmN])
  simp only [hφ] at hboundary
  have hnormcenter (j : ℤ) : ‖(Real.pi : ℂ)*j‖ = Real.pi*|(j : ℝ)| := by
    have he : (Real.pi : ℂ)*j = ((Real.pi*(j : ℝ) : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos]
  have hnormz : ‖z‖ ≤ Real.pi*|(n : ℝ)|+Real.pi/5 := by
    have h := norm_add_le (z-(Real.pi : ℂ)*n) ((Real.pi : ℂ)*n)
    rw [sub_add_cancel, hnormcenter] at h
    linarith
  let U : ℝ := (|(n : ℝ)|+N+2/5)*Real.pi
  let D : ℝ := (|(n : ℝ)|-N+3/10)*Real.pi
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hD : 0 < D := by dsimp [D]; apply mul_pos _ Real.pi_pos; linarith
  have hupper (u : ℂ) (hu : ‖u-(Real.pi : ℂ)*m‖ ≤ Real.pi/5) : ‖u-z‖ ≤ U := by
    have h := norm_add_le (u-(Real.pi : ℂ)*m) ((Real.pi : ℂ)*m)
    rw [sub_add_cancel, hnormcenter, hmN] at h
    dsimp [U]
    nlinarith [norm_sub_le u z]
  have hnum : ‖sourceStandardRoot (by simp) (by norm_num) ψ m z‖ ≤ U :=
    section28_standardRoot_norm_upper (by simp) (by norm_num) ψ m z U hU
      (hupper _ (hboundary.1.trans hboundary.2.2.le))
      (hupper _ (hboundary.2.1.trans hboundary.2.2.le))
  have hcentral := H1_canonicalEndpoints_cutoff_central_re φ heven N hN k hk
  simp only [hφ] at hcentral
  have hden : D ≤ ‖sourceStandardRoot (by simp) (by norm_num) ψ k z‖ := by
    have hh := section28_standardRoot_norm_lower_of_abs_re (by simp) (by norm_num) ψ k z
      (((N : ℝ)-1/2)*Real.pi) hcentral.1 hcentral.2 (by nlinarith [Real.pi_pos])
    apply le_trans _ hh
    dsimp [D]
    nlinarith
  have hratio : U/D = (|(n : ℝ)|+N+2/5)/(|(n : ℝ)|-N+3/10) := by
    dsimp [U, D]
    exact mul_div_mul_right _ _ Real.pi_ne_zero
  rw [norm_div, ← hratio]
  apply (div_le_iff₀ (hD.trans_le hden)).mpr
  calc
    _ ≤ U := hnum
    _ = U/D*D := (div_mul_cancel₀ U hD.ne').symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hden (div_nonneg hU hD.le)

/-- The negative-index counterpart uses the opposite enclosing roots of
the same complex source and the absolute-index rational expression. -/
theorem section28_complex_enclosing_root_ratio_negative
    (ψ : CoeffPair 2)
    (φ : WeightedCoeffPair (SpectralWeight.piSobolev 1 (by norm_num)).toWeight 2)
    (hφ : weightedBaseToPair (SpectralWeight.piSobolev 1 (by norm_num)) φ = periodOnePotential ψ)
    (N : ℕ) (hNpos : 1 ≤ N) (hN : 8*‖φ‖^2 ≤ 1+(N : ℝ))
    (n : ℤ) (hn : n ≤ -(N : ℤ)) (z : ℂ)
    (hz : z ∈ sourcePeriodicSegment (by simp) (by norm_num) ψ n) :
    ‖sourceStandardRoot (by simp) (by norm_num) ψ (N : ℤ) z /
      sourceStandardRoot (by simp) (by norm_num) ψ (-(N : ℤ)+1) z‖ ≤
      (|(n : ℝ)|+N+2/5)/(|(n : ℝ)|-N+3/10) :=
  section28_complex_enclosing_root_ratio_signed ψ φ hφ N hN _ _ n
    (by simp) (by omega) (by omega) z hz

end NLS.ZakharovShabat
