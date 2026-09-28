import NLS.ZakharovShabat.SourcePsiCandidateEntireVariation

/-!
# Root-direction derivative of the finite psi products

The deleted psi numerator is a locally uniform limit of finite
products. At each cutoff the derivative in a root-sequence direction
is the sum obtained by differentiating one retained factor at a time.
This exact finite identity is the starting point for the resolvent
series and outer-circle bound in Lemma 12.7.
-/

noncomputable section
open Complex Set Filter Topology Metric
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Differentiating one spectral factor along an affine root-sequence
line contributes the corresponding coordinate divided by its fixed
normalizing denominator. -/
theorem hasDerivAt_singleSpectralFactor_rootLine
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a h : Coeff p) (z : ℂ) (m : ℤ) :
    HasDerivAt
      (fun t : ℂ => singleSpectralFactor
        (displacedRoots (a + t • h)) z m)
      (h m / singleSpectralDenominator m) 0 := by
  have hroot : HasDerivAt
      (fun t : ℂ => displacedRoots (a + t • h) m) (h m) 0 := by
    have heq : (fun t : ℂ => displacedRoots (a + t • h) m) =
        (fun t : ℂ => displacedRoots a m + t * h m) := by
      funext t
      simp only [displacedRoots, lp.coeFn_add, Pi.add_apply,
        lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (h m)).const_add
      (displacedRoots a m)
  simpa only [singleSpectralFactor] using
    (hroot.sub_const z).div_const (singleSpectralDenominator m)

/-- The finite product rule in a root-sequence direction, with no
noncollision assumption on the roots. -/
theorem deriv_finiteSingleSpectralProduct_rootLine
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (s : Finset ℤ) (a h : Coeff p) (z : ℂ) :
    deriv (fun t : ℂ => ∏ m ∈ s,
      singleSpectralFactor (displacedRoots (a + t • h)) z m) 0 =
      ∑ m ∈ s,
        (∏ j ∈ s.erase m,
          singleSpectralFactor (displacedRoots a) z j) *
          (h m / singleSpectralDenominator m) := by
  have hprod := HasDerivAt.fun_finsetProd (u := s)
    (fun m _ => hasDerivAt_singleSpectralFactor_rootLine a h z m)
  simpa only [zero_smul, add_zero, smul_eq_mul] using hprod.deriv

/-- The literal deleted cutoff has the same finite derivative sum,
including the exceptional zero-mode normalization. -/
theorem deriv_sourcePsiCandidate_cutoff_rootLine
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (n : ℤ) (N : ℕ) (a h : Coeff p) (z : ℂ) :
    deriv (fun t : ℂ => -2 *
      jointDeletedSingleSpectralPartialProduct n N (z,a + t • h)) 0 =
      (-2 / singleSpectralDenominator n) *
        ∑ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
          (∏ j ∈ ((Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n).erase m,
            singleSpectralFactor (displacedRoots a) z j) *
            (h m / singleSpectralDenominator m) := by
  have heq : (fun t : ℂ => -2 *
      jointDeletedSingleSpectralPartialProduct n N (z,a + t • h)) =
      fun t : ℂ => (-2 / singleSpectralDenominator n) *
        ∏ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
          singleSpectralFactor (displacedRoots (a + t • h)) z m := by
    funext t
    unfold jointDeletedSingleSpectralPartialProduct
    ring
  rw [heq, deriv_const_mul_field]
  exact congrArg ((-2 / singleSpectralDenominator n) * ·)
    (deriv_finiteSingleSpectralProduct_rootLine
      ((Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n) a h z)

/-- The derivatives of the literal deleted cutoffs converge to the
entire psi-numerator variation at every spectral parameter. -/
theorem tendsto_deriv_sourcePsiCandidate_cutoff_rootLine
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a h : Coeff p) (z : ℂ) :
    Tendsto
      (fun N : ℕ => deriv (fun t : ℂ => -2 *
        jointDeletedSingleSpectralPartialProduct n N (z,a + t • h)) 0)
      atTop (𝓝 (sourcePsiCandidateVariation n a h z)) := by
  let F : ℕ → ℂ → ℂ := fun N t =>
    jointDeletedSingleSpectralPartialProduct n N (z,a + t • h)
  let f : ℂ → ℂ := fun t => jointDeletedSingleSpectralProduct n (z,a + t • h)
  have hlocal : TendstoLocallyUniformlyOn F f atTop Set.univ := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ hK
    obtain ⟨B,hB⟩ := hK.isBounded.exists_norm_le
    let S : Set (Coeff p) := (fun t : ℂ => a + t • h) '' K
    let R : ℝ := ‖a‖ + max B 0 * ‖h‖
    have hR : 0 ≤ R := by dsimp [R]; positivity
    have hb : ∀ b ∈ S, ‖b‖ ≤ R := by
      rintro b ⟨t,ht,rfl⟩
      calc
        ‖a + t • h‖ ≤ ‖a‖ + ‖t • h‖ := norm_add_le _ _
        _ = ‖a‖ + ‖t‖ * ‖h‖ := by rw [norm_smul]
        _ ≤ R := by
          dsimp [R]
          gcongr
          exact (hB t ht).trans (le_max_left _ _)
    have hu := (tendstoUniformlyOn_jointDeletedSingleSpectralProduct
      hp hp1 n ({z} : Set ℂ) isCompact_singleton S R hR hb).comp
        (fun t : ℂ => (z,a + t • h))
    have hsub : K ⊆
        (fun t : ℂ => (z,a + t • h)) ⁻¹' (({z} : Set ℂ) ×ˢ S) := by
      intro t ht
      exact ⟨rfl,⟨t,ht,rfl⟩⟩
    exact hu.mono hsub
  have hdiff (N : ℕ) : DifferentiableOn ℂ (F N) Set.univ := by
    intro t _
    have hline : AnalyticAt ℂ (fun w : ℂ => (z,a + w • h)) t :=
      analyticAt_const.prod
        (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
    exact ((analyticOnNhd_jointDeletedSingleSpectralPartialProduct n N
      (z,a + t • h) (mem_univ _)).comp_of_eq hline
        (by simp)).differentiableAt.differentiableWithinAt
  have hderiv := (hlocal.deriv (Eventually.of_forall hdiff) isOpen_univ).tendsto_at
    (mem_univ (0 : ℂ))
  have hscaled := hderiv.const_mul (-2 : ℂ)
  have heN (N : ℕ) :
      deriv (fun t : ℂ => -2 *
        jointDeletedSingleSpectralPartialProduct n N (z,a + t • h)) 0 =
      -2 * deriv (F N) 0 := by
    rw [deriv_const_mul_field]
  have heLimit : sourcePsiCandidateVariation n a h z =
      -2 * deriv f 0 := by
    rw [sourcePsiCandidateVariation_eq_line_deriv hp hp1]
    change deriv (fun t : ℂ => -2 * f t) 0 = _
    rw [deriv_const_mul_field]
  simpa only [Function.comp_apply, ← heN, ← heLimit] using hscaled

/-- The explicit finite product-rule sums converge to the entire
psi-numerator variation. -/
theorem tendsto_sourcePsiCandidateVariation_finiteSums
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (n : ℤ) (a h : Coeff p) (z : ℂ) :
    Tendsto
      (fun N : ℕ => (-2 / singleSpectralDenominator n) *
        ∑ m ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n,
          (∏ j ∈ ((Finset.Icc (-(N : ℤ)) (N : ℤ)).erase n).erase m,
            singleSpectralFactor (displacedRoots a) z j) *
            (h m / singleSpectralDenominator m))
      atTop (𝓝 (sourcePsiCandidateVariation n a h z)) := by
  simpa only [deriv_sourcePsiCandidate_cutoff_rootLine] using
    tendsto_deriv_sourcePsiCandidate_cutoff_rootLine hp hp1 n a h z

end NLS.ZakharovShabat
