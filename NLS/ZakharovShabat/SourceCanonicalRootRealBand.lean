import NLS.ZakharovShabat.SourceRealBandGeometry
import NLS.ZakharovShabat.SourceCriticalRootGapNeighborhood

/-! # The canonical square root on a real spectral band

Continuity transports the omitted product's sign from the right gap
endpoint into the neighboring band. This fixes the canonical root's
imaginary sign and its exact expression by the positive real square root.
-/
noncomputable section
open Set Filter Topology Complex ComplexConjugate NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The omitted product is real at every real point of its domain,
including points between gaps rather than just on the selected gap. -/
theorem sourceStandardRootOmittedProduct_im_eq_zero_on_real_domain
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (x : ℝ)
    (hx : (x : ℂ) ∈ sourceStandardRootOmittedDomain hp hp1 φ n) :
    (sourceStandardRootOmittedProduct hp hp1 n φ (x : ℂ)).im = 0 := by
  have hroot (m : ℤ) (hm : m ≠ n) : (sourceStandardRoot hp hp1 φ m (x : ℂ)).im = 0 := by
    apply sourceStandardRoot_im_eq_zero_of_real_exterior hp hp1 φ hφ m x
    by_contra h
    push Not at h
    exact hx m hm (sourcePeriodicSegment_mem_of_realIcc hp hp1 φ hφ m x ⟨h.1,h.2⟩)
  have hden (m : ℤ) : conj (singleSpectralDenominator m) = singleSpectralDenominator m := by
    unfold singleSpectralDenominator
    split_ifs <;> simp
  have hfinite (N : ℕ) : conj (sourceStandardRootOmittedPartialProduct hp hp1 n N ((x : ℂ),φ)) =
      sourceStandardRootOmittedPartialProduct hp hp1 n N ((x : ℂ),φ) := by
    unfold sourceStandardRootOmittedPartialProduct
    rw [map_div₀,map_prod,hden]
    congr 1
    apply Finset.prod_congr rfl
    intro m hm
    rw [map_div₀,hden,Complex.conj_eq_iff_im.mpr (hroot m (Finset.mem_erase.mp hm).1)]
  have ht := tendsto_sourceStandardRootOmittedPartialProduct hp hp1 n φ (x : ℂ)
  have hc := continuous_conj.continuousAt.tendsto.comp ht
  simp only [Function.comp_def,hfinite] at hc
  exact Complex.conj_eq_iff_im.mp (tendsto_nhds_unique hc ht)

/-- The parity sign at the closed left gap persists all the way across
the neighboring band, up to but excluding the next gap. -/
theorem sourceStandardRootOmittedProduct_signed_re_pos_on_realBand
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ Ico
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) (n+1)).re) :
    0 < (-1 : ℝ)^n.natAbs * (sourceStandardRootOmittedProduct hp hp1 n φ (x : ℂ)).re := by
  let a := (canonicalPeriodicRight hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n).re
  let f : ℝ → ℝ := fun y => (-1 : ℝ)^n.natAbs *
    (sourceStandardRootOmittedProduct hp hp1 n φ (y : ℂ)).re
  have hdom (y : ℝ) (hy : y ∈ Icc a x) :
      (y : ℂ) ∈ sourceStandardRootOmittedDomain hp hp1 φ n :=
    sourceRealBand_leftClosed_subset_omittedDomain hp hp1 φ hφ n y ⟨hy.1,hy.2.trans_lt hx.2⟩
  obtain ⟨W,_,_,hreal,hdata⟩ := exists_global_source_analytic_omittedJointProduct hp hp1
  have hP := sourceStandardRootOmittedProduct_analyticOnNhd_spectral hp hp1 n W (hdata n).2.1 φ (hreal hφ)
  have hc : ContinuousOn f (Icc a x) := by
    intro y hy
    exact continuousWithinAt_const.mul
      (continuous_re.continuousAt.comp ((hP _ (hdom y hy)).continuousAt.comp
        continuous_ofReal.continuousAt)).continuousWithinAt
  have hstart : 0 < f a := sourceStandardRootOmittedProduct_signed_re_pos_on_realGap_closedGap
    hp hp1 φ hφ n a ⟨re_le_of_complexLexLE
      ((canonicalPeriodicEndpoints_spec hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ)).2.1 n),le_rfl⟩
  by_contra h
  have hend : f x ≤ 0 := le_of_not_gt h
  obtain ⟨y,hy,hzero⟩ := intermediate_value_Icc' hx.1 hc ⟨hend,hstart.le⟩
  have hre : (sourceStandardRootOmittedProduct hp hp1 n φ (y : ℂ)).re = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ (by norm_num))
  apply sourceStandardRootOmittedProduct_ne_zero hp hp1 φ (y : ℂ) n (hdom y hy)
  exact Complex.ext hre (sourceStandardRootOmittedProduct_im_eq_zero_on_real_domain hp hp1 φ hφ n y (hdom y hy))

/-- In the band following gap `n`, the root is purely imaginary and
its imaginary part has sign `-(-1)^n`. -/
theorem sourceCanonicalRoot_realBand_sign
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ sourceRealBand hp hp1 φ n) :
    (sourceCanonicalRoot hp hp1 φ (x : ℂ)).re = 0 ∧
      (-1 : ℝ)^n.natAbs * (sourceCanonicalRoot hp hp1 φ (x : ℂ)).im < 0 := by
  have hdom := sourceRealBand_leftClosed_subset_omittedDomain hp hp1 φ hφ n x ⟨hx.1.le,hx.2⟩
  have hPim := sourceStandardRootOmittedProduct_im_eq_zero_on_real_domain hp hp1 φ hφ n x hdom
  have hPpos := sourceStandardRootOmittedProduct_signed_re_pos_on_realBand hp hp1 φ hφ n x ⟨hx.1.le,hx.2⟩
  have hwim := sourceStandardRoot_im_eq_zero_of_real_exterior hp hp1 φ hφ n x (Or.inr hx.1)
  have hwneg := sourceStandardRoot_re_neg_of_real_gt_right hp hp1 φ hφ n x hx.1
  rw [sourceCanonicalRoot_eq_omitted hp hp1 n]
  constructor
  · simp [Complex.mul_re,Complex.mul_im,hPim,hwim]
  · simp only [Complex.mul_re,Complex.mul_im,hPim,hwim]
    norm_num
    have h := mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by norm_num : (0 : ℝ) < 2) hwneg) hPpos
    convert! h using 1
    ring

/-- The discriminant lies strictly between its periodic levels on
every real band, including bands adjacent to collapsed gaps. -/
theorem sourceDiscriminant_realBand_sq_lt_four
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ sourceRealBand hp hp1 φ n) :
    (canonicalDiscriminant hp (periodOnePotential φ) (x : ℂ)).re ^ 2 < 4 := by
  have hs := congrArg Complex.re (sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four hp hp1 φ (x : ℂ)
    (sourceRealBand_subset_rootDomain hp hp1 φ hφ n x hx))
  have hsign := sourceCanonicalRoot_realBand_sign hp hp1 φ hφ n x hx
  have hdreal := canonicalDiscriminant_im_eq_zero_of_realType hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) x
  have hne : (sourceCanonicalRoot hp hp1 φ (x : ℂ)).im ≠ 0 := by
    intro he
    rw [he,mul_zero] at hsign
    exact lt_irrefl 0 hsign.2
  simp only [pow_two,Complex.mul_re,Complex.sub_re,hsign.1,hdreal,mul_zero,sub_zero] at hs
  norm_num at hs
  have hs' : -(sourceCanonicalRoot hp hp1 φ (x : ℂ)).im^2 =
      (canonicalDiscriminant hp (periodOnePotential φ) (x : ℂ)).re^2-4 := by
    simpa only [pow_two] using! hs
  nlinarith [sq_pos_of_ne_zero hne]

/-- The exact oriented square-root expression used in the adjacent-band
arcsine integral calculation. -/
theorem sourceCanonicalRoot_eq_signed_sqrt_on_realBand
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) (n : ℤ) (x : ℝ)
    (hx : x ∈ sourceRealBand hp hp1 φ n) :
    sourceCanonicalRoot hp hp1 φ (x : ℂ) =
      -I*(((-1 : ℝ)^n.natAbs * Real.sqrt
        (4-(canonicalDiscriminant hp (periodOnePotential φ) (x : ℂ)).re ^ 2) : ℝ) : ℂ) := by
  let s : ℝ := (-1)^n.natAbs
  let y := (sourceCanonicalRoot hp hp1 φ (x : ℂ)).im
  have hsign := sourceCanonicalRoot_realBand_sign hp hp1 φ hφ n x hx
  have hss : s^2 = 1 := by dsimp [s]; rw [← pow_mul]; simp [mul_comm _ 2, pow_mul]
  have hs := congrArg Complex.re (sourceCanonicalRoot_sq_eq_discriminant_sq_sub_four hp hp1 φ (x : ℂ)
    (sourceRealBand_subset_rootDomain hp hp1 φ hφ n x hx))
  have hdreal := canonicalDiscriminant_im_eq_zero_of_realType hp hp1 (periodOnePotential φ)
    (periodOnePotential_mem φ) (isRealType_periodOnePotential φ hφ) x
  have hsq : (-s*y)^2 = 4-(canonicalDiscriminant hp (periodOnePotential φ) (x : ℂ)).re^2 := by
    simp only [pow_two,Complex.mul_re,Complex.sub_re,hsign.1,hdreal,mul_zero,sub_zero] at hs
    norm_num at hs
    calc
      (-s*y)^2 = s^2*y^2 := by ring
      _ = y^2 := by rw [hss,one_mul]
      _ = _ := by dsimp [y]; nlinarith [hs]
  have hnonneg : 0 ≤ -s*y := by simpa only [neg_mul] using le_of_lt (neg_pos.mpr hsign.2)
  have hroot : Real.sqrt (4-(canonicalDiscriminant hp (periodOnePotential φ) (x : ℂ)).re^2) = -s*y := by
    rw [← hsq,Real.sqrt_sq hnonneg]
  apply Complex.ext
  · simpa only [Complex.mul_re,Complex.neg_re,Complex.I_re,Complex.ofReal_im,
      neg_zero,zero_mul,mul_zero,sub_zero] using hsign.1
  · simp only [Complex.mul_im,Complex.I_re,Complex.neg_im,Complex.I_im,
      Complex.ofReal_im,Complex.ofReal_re,zero_mul,neg_mul,one_mul,zero_add]
    rw [hroot]
    change y = -(s*(-s*y))
    calc
      y = s^2*y := by rw [hss,one_mul]
      _ = _ := by ring

end NLS.ZakharovShabat
