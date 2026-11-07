import NLS.RealAnalysis.SplitRootGap
import NLS.KdV.PseudomeasureCouplingLipschitz
import NLS.KdV.PseudomeasureDiagonalRootConjugation
import NLS.KdV.PseudomeasureRealPairs

/-! Two-sided comparison of the ACTUAL real Hill gap with the actual coupling
at the constructed diagonal root,including every collapsed gap. -/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.KdV

/-- The real part of the actual diagonal on the physical real spectral axis. -/
def endpointRealDiagonal (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (x : ℝ) : ℝ :=
  (endpointDiagonal r hr hr1 n (q,(x:ℂ))).re

/-- The nonnegative size of the ACTUAL upper coupling on the real spectral axis. -/
def endpointRealCoupling (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2) (n : ℕ)
    (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (x : ℝ) : ℝ :=
  ‖endpointUpperCoupling r hr hr1 n (q,(x:ℂ))‖

/-- The actual reduced matrix is Hermitian on the real axis at real data. -/
theorem endpointCoefficients_real_axis (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (hq : endpointConjugate SpectralWeight.one r q = q) (x : ℝ) (hx : (x:ℂ) ∈ reducedHillStrip n) :
    endpointDiagonal r hr hr1 n (q,(x:ℂ)) = (endpointRealDiagonal r hr hr1 n q x:ℂ) ∧
      endpointLowerCoupling r hr hr1 n (q,(x:ℂ)) = (starRingEnd ℂ) (endpointUpperCoupling r hr hr1 n (q,(x:ℂ))) := by
  have he := endpointCoefficients_conj r hr hr1 n hn (x:ℂ) hx q hs
  rw [hq, Complex.conj_ofReal] at he
  have him : (endpointDiagonal r hr hr1 n (q,(x:ℂ))).im = 0 := by
    have hh := congrArg Complex.im he.1
    simp only [Complex.conj_im] at hh
    linarith
  exact ⟨Complex.ext rfl him, he.2.2⟩

/-- Actual determinant zeros are precisely the two real scalar branch zeros. -/
theorem endpointReducedDeterminant_real_zero_iff (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (hq : endpointConjugate SpectralWeight.one r q = q) (x : ℝ) (hx : (x:ℂ) ∈ reducedHillStrip n) :
    endpointReducedDeterminant r hr hr1 n (q,(x:ℂ)) = 0 ↔
      x-freeHillValue n-endpointRealDiagonal r hr hr1 n q x+endpointRealCoupling r hr hr1 n q x = 0 ∨
      x-freeHillValue n-endpointRealDiagonal r hr hr1 n q x-endpointRealCoupling r hr hr1 n q x = 0 := by
  obtain ⟨ha, hb⟩ := endpointCoefficients_real_axis r hr hr1 n hn q hs hq x hx
  have hprod : endpointUpperCoupling r hr hr1 n (q,(x:ℂ))*endpointLowerCoupling r hr hr1 n (q,(x:ℂ)) =
      (((endpointRealCoupling r hr hr1 n q x)^2:ℝ):ℂ) := by
    rw [hb, Complex.mul_conj']
    simp only [endpointRealCoupling, Complex.ofReal_pow]
  have hd : endpointReducedDeterminant r hr hr1 n (q,(x:ℂ)) =
      (((x-freeHillValue n-endpointRealDiagonal r hr hr1 n q x)^2-(endpointRealCoupling r hr hr1 n q x)^2:ℝ):ℂ) := by
    rw [endpointReducedDeterminant_factorization r hr hr1 n hn q hs (x:ℂ) hx, ha, hprod]
    push_cast
    rfl
  rw [hd, Complex.ofReal_eq_zero]
  rw [show (x-freeHillValue n-endpointRealDiagonal r hr hr1 n q x)^2-(endpointRealCoupling r hr hr1 n q x)^2 =
    (x-freeHillValue n-endpointRealDiagonal r hr hr1 n q x+endpointRealCoupling r hr hr1 n q x)*
    (x-freeHillValue n-endpointRealDiagonal r hr hr1 n q x-endpointRealCoupling r hr hr1 n q x) by ring,
    mul_eq_zero]

/-- The constructed alpha brackets the ACTUAL spectral endpoints,and its
actual coupling is comparable with the actual gap. No open-gap assumption. -/
theorem EndpointHillRealPair.adapted_gap_comparison (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1/2)
    (n : ℕ) (hn : 1 ≤ n) (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤)
    (hs : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖ ≤ 1/2)
    (hq : endpointConjugate SpectralWeight.one r q = q) (p : EndpointHillRealPair r hr hr1 q n) :
    p.left ≤ (endpointHillDiagonalRoot r hr hr1 n hn q).re ∧
      (endpointHillDiagonalRoot r hr hr1 n hn q).re ≤ p.right ∧
      ‖endpointUpperCoupling r hr hr1 n (q,endpointHillDiagonalRoot r hr hr1 n hn q)‖ ≤ p.right-p.left ∧
      p.right-p.left ≤ 3*‖endpointUpperCoupling r hr hr1 n (q,endpointHillDiagonalRoot r hr hr1 n hn q)‖ := by
  let a := endpointRealDiagonal r hr hr1 n q
  let b := endpointRealCoupling r hr hr1 n q
  let α := (endpointHillDiagonalRoot r hr hr1 n hn q).re
  let I := Icc (freeHillValue n-6*(n:ℝ)) (freeHillValue n+6*(n:ℝ))
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hSQ : Real.sqrt (n:ℝ) ≤ n := Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩
  have hstrip (x : ℝ) (hx : x ∈ I) : (x:ℂ) ∈ reducedHillStrip n := by
    change |x-freeHillValue n| ≤ 6*(n:ℝ)
    exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hI (x : ℝ) (hx : (x:ℂ) ∈ reducedHillStrip n) : x ∈ I := by
    have hh : |x-freeHillValue n| ≤ 6*(n:ℝ) := hx
    have hh' := abs_le.mp hh
    exact ⟨by linarith, by linarith⟩
  have haL (x : ℝ) (hx : x ∈ I) (y : ℝ) (hy : y ∈ I) : |a x-a y| ≤ (1/8:ℝ)*|x-y| := by
    have hh := (Complex.abs_re_le_norm (endpointDiagonal r hr hr1 n (q,(x:ℂ))-
      endpointDiagonal r hr hr1 n (q,(y:ℂ)))).trans
      (endpointDiagonal_sub_le_eighth r hr hr1 n hn (x:ℂ) (y:ℂ) (hstrip x hx) (hstrip y hy) q hs)
    simpa only [a, endpointRealDiagonal, Complex.sub_re, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hh
  have hbL (x : ℝ) (hx : x ∈ I) (y : ℝ) (hy : y ∈ I) : |b x-b y| ≤ (1/8:ℝ)*|x-y| := by
    have hh := (abs_norm_sub_norm_le (endpointUpperCoupling r hr hr1 n (q,(x:ℂ)))
      (endpointUpperCoupling r hr hr1 n (q,(y:ℂ)))).trans
      (endpointUpperCoupling_sub_le_eighth r hr hr1 n hn (x:ℂ) (y:ℂ) (hstrip x hx) (hstrip y hy) q hs)
    simpa only [b, endpointRealCoupling, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hh
  have haB (x : ℝ) (hx : x ∈ I) : |a x| ≤ (6*(n:ℝ))/4 := by
    have hh := (Complex.abs_re_le_norm (endpointDiagonal r hr hr1 n (q,(x:ℂ)))).trans
      (norm_endpointDiagonal_le_two_norm r hr hr1 n hn q hs (x:ℂ) (hstrip x hx))
    have hqn := endpointHill_norm_le_index_sixteenth r hr hr1 n hn q hs
    dsimp [a, endpointRealDiagonal]
    linarith
  have hbB (x : ℝ) (hx : x ∈ I) : 0 ≤ b x ∧ b x ≤ (6*(n:ℝ))/4 := by
    have hh := (norm_fst_le (hillModeCoordinates (SpectralWeight.one.negativeSobolev r) ⊤ n
      (endpointHillEffectivePotential r hr hr1 n hn (x:ℂ) (hstrip x hx) q hs (0,1)))).trans
      (endpointHillEffectiveCorrection_columns_le r hr hr1 n hn (x:ℂ) (hstrip x hx) q hs).2
    have hsmall := endpoint_effective_column_small r hr hr1 n hn q hs
    have hnorm : b x ≤ 2*Weight.sobolev r (2*(n:ℤ))*‖q‖ := by
      simpa only [b, endpointRealCoupling, endpointUpperCoupling, hillModeCoordinates_apply,
        endpointEffectiveFamily_eq r hr hr1 n hn (q,(x:ℂ)) (hstrip x hx) hs] using hh
    exact ⟨norm_nonneg _, by linarith⟩
  obtain ⟨hαstrip, hroot, _⟩ := endpointHillDiagonalRoot_spec r hr hr1 n hn q hs
  have hαc : (α:ℂ) = endpointHillDiagonalRoot r hr hr1 n hn q :=
    Complex.ext rfl (by simpa only [Complex.ofReal_im] using (endpointHillDiagonalRoot_im_eq_zero r hr hr1 n hn q hs hq).symm)
  have hαI : α ∈ I := hI α (hαc.symm ▸ hαstrip)
  have hαeq : α-freeHillValue n-a α = 0 := by
    have hh := congrArg Complex.re hroot
    rw [← hαc] at hh
    simp only [Complex.add_re, Complex.ofReal_re] at hh
    dsimp [a, endpointRealDiagonal]
    linarith
  obtain ⟨l, hl, u, hu, hlα, hαu, hzeros, hlow, hupp⟩ :=
    NLS.RealAnalysis.exists_split_roots_gap_comparison a b (freeHillValue n) (6*(n:ℝ)) α
      (by positivity) haL hbL haB hbB hαI hαeq
  have hziff (x : ℝ) (hx : x ∈ I) : endpointReducedDeterminant r hr hr1 n (q,(x:ℂ)) = 0 ↔ x = l ∨ x = u := by
    rw [endpointReducedDeterminant_real_zero_iff r hr hr1 n hn q hs hq x (hstrip x hx)]
    exact or_congr (hzeros x hx).1 (hzeros x hx).2
  have hpl := (hziff p.left (hI p.left p.left_mem)).mp (p.left_zero r hr hr1 n hn q hs)
  have hpr := (hziff p.right (hI p.right p.right_mem)).mp (p.right_zero r hr hr1 n hn q hs)
  have hsl := (p.spectrum_iff l (hstrip l hl)).mp
    ((mem_endpointHillSpectrum_iff_determinant r hr hr1 n hn l (hstrip l hl) q hs).mpr ((hziff l hl).mpr (Or.inl rfl)))
  have hsu := (p.spectrum_iff u (hstrip u hu)).mp
    ((mem_endpointHillSpectrum_iff_determinant r hr hr1 n hn u (hstrip u hu) q hs).mpr ((hziff u hu).mpr (Or.inr rfl)))
  simp only [Complex.ofReal_inj] at hsl hsu
  have he : l = p.left ∧ u = p.right := by
    rcases hpl with hpl | hpl <;> rcases hpr with hpr | hpr <;>
      rcases hsl with hsl | hsl <;> rcases hsu with hsu | hsu <;>
      constructor <;> linarith [p.ordered]
  have hbα : b α = ‖endpointUpperCoupling r hr hr1 n (q,endpointHillDiagonalRoot r hr hr1 n hn q)‖ := by
    dsimp [b, endpointRealCoupling]
    rw [hαc]
  exact ⟨by simpa only [he.1] using hlα, by simpa only [he.2] using hαu,
    by simpa only [he.1, he.2, hbα] using hlow,
    by simpa only [he.1, he.2, hbα] using hupp⟩

end NLS.KdV
