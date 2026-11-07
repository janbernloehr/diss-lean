import NLS.Articles.DNLSEstimates.FiniteGap
import NLS.ZakharovShabat.SourceCriticalRootRatioOpenGapDomain
import NLS.ZakharovShabat.SourceStandardRootContourAnyCircle
import NLS.ComplexAnalysis.ExteriorInversionRemainder
import NLS.ZakharovShabat.SourceSobolevClassicalCompatibility

/-!
# Exterior geometry for complex finite-gap sources

Finite-gap here restricts the actual periodic gaps, with no real-type or
smoothness assumption. The continued discriminant quotient is a finite
product and has a holomorphic inversion germ with value `-i`.
-/
noncomputable section
open Set Complex Metric Filter Topology NLS.ZakharovShabat
open scoped ENNReal ContDiff
namespace NLS.Articles.DNLSEstimates
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The complex finite-gap condition concerns the actual periodic gaps. -/
def ComplexFiniteGap (hp : p ≠ ⊤) (hp1 : 1 < p) (a : CoeffPair p) : Prop :=
  {n : ℤ | canonicalPeriodicGap hp hp1 (periodOnePotential a)
    (periodOnePotential_mem a) n ≠ 0}.Finite

/-- Compactness of the removed cuts does not require real spectral endpoints. -/
theorem complex_finiteGap_compact_cuts (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : CoeffPair p) (hf : ComplexFiniteGap hp hp1 a) :
    IsCompact (sourceOpenGapComplement hp hp1 a)ᶜ := by
  have he : (sourceOpenGapComplement hp hp1 a)ᶜ =
      ⋃ n ∈ {n : ℤ | canonicalPeriodicGap hp hp1 (periodOnePotential a)
        (periodOnePotential_mem a) n ≠ 0}, sourcePeriodicSegment hp hp1 a n := by
    ext z
    simp [sourceOpenGapComplement]
  rw [he]
  exact hf.isCompact_biUnion fun n _ => isCompact_sourcePeriodicSegment hp hp1 a n

/-- One full exterior region avoids all noncollapsed complex cuts. -/
theorem complex_finiteGap_exterior (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : CoeffPair p) (hf : ComplexFiniteGap hp hp1 a) :
    ∃ R : ℝ, 0 < R ∧ {z : ℂ | R < ‖z‖} ⊆ sourceOpenGapComplement hp hp1 a := by
  obtain ⟨B,hB⟩ := (complex_finiteGap_compact_cuts hp hp1 a hf).isBounded.exists_norm_le
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro z hz
  by_contra hn
  exact (not_lt_of_ge ((hB z hn).trans (le_max_left _ _))) hz

/-- The inverted individual critical-root factor, defined also at zero. -/
def invertedCriticalFactor (t g c u : ℂ) : ℂ :=
  (1-c*u)*shiftedInverseRootFactor t g 0 u

@[simp] theorem invertedCriticalFactor_zero (t g c : ℂ) :
    invertedCriticalFactor t g c 0 = 1 := by
  simp [invertedCriticalFactor]

theorem invertedCriticalFactor_analyticAt_zero (t g c : ℂ) :
    AnalyticAt ℂ (invertedCriticalFactor t g c) 0 :=
  (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).mul
    (shiftedInverseRootFactor_analyticAt_zero t g 0)

/-- This germ is the actual factor, rather than a formal square root series. -/
theorem invertedCriticalFactor_eq (t g c z : ℂ) (hz : z ≠ 0) (hzt : z ≠ t) :
    invertedCriticalFactor t g c z⁻¹ = (c-z)/normalizedStandardRoot t g z := by
  rw [div_eq_mul_inv, normalizedRoot_inv_shifted_factor t g 0 z hz hzt]
  simp only [sub_zero]
  unfold invertedCriticalFactor
  have he : (c-z)*(-z⁻¹) = 1-c*z⁻¹ := by field_simp; ring
  rw [← mul_assoc, he]

/-- All closed factors cancel before taking the product, including their endpoints. -/
theorem complex_finiteGap_continued_eq_prod (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : CoeffPair p) (hf : ComplexFiniteGap hp hp1 a) (z : ℂ) :
    sourceCriticalRootRatioContinued hp hp1 a z =
      -I * ∏ n ∈ hf.toFinset, (canonicalCriticalPoints hp hp1
        (periodOnePotential a) (periodOnePotential_mem a) n-z)/sourceStandardRoot hp hp1 a n z := by
  classical
  unfold sourceCriticalRootRatioContinued
  rw [tprod_eq_prod (s := hf.toFinset) (fun n hn => ?_)]
  · congr 1
    apply Finset.prod_congr rfl
    intro n hn
    have hg : canonicalPeriodicGap hp hp1 (periodOnePotential a)
        (periodOnePotential_mem a) n ≠ 0 := (hf.mem_toFinset).mp hn
    simp only [sourceCriticalRootRegularizedFactor, if_neg hg]
  · have hg : canonicalPeriodicGap hp hp1 (periodOnePotential a)
        (periodOnePotential_mem a) n = 0 := by simpa using hn
    simp only [sourceCriticalRootRegularizedFactor, if_pos hg]

/-- Every complex finite-gap source has an actual normalized holomorphic
inversion germ. No physical regularity of the potential is assumed. -/
theorem complex_finiteGap_quotient_germ (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : CoeffPair p) (hf : ComplexFiniteGap hp hp1 a) :
    ∃ r : ℝ, 0 < r ∧ ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball 0 r) ∧ g 0 = -I ∧
      ∀ᶠ z : ℂ in Bornology.cobounded ℂ,
        sourceCriticalRootRatioContinued hp hp1 a z = g z⁻¹ := by
  classical
  let t := canonicalPeriodicMidpoint hp hp1 (periodOnePotential a) (periodOnePotential_mem a)
  let c := canonicalCriticalPoints hp hp1 (periodOnePotential a) (periodOnePotential_mem a)
  let gap := canonicalPeriodicGap hp hp1 (periodOnePotential a) (periodOnePotential_mem a)
  let g : ℂ → ℂ := fun u => -I * ∏ n ∈ hf.toFinset, invertedCriticalFactor (t n) (gap n ^ 2) (c n) u
  have hg : AnalyticAt ℂ g 0 := by
    apply analyticAt_const.mul
    exact
      (Finset.analyticAt_fun_prod hf.toFinset fun n _ => invertedCriticalFactor_analyticAt_zero (t n) (gap n ^ 2) (c n))
  obtain ⟨r,hr,hgr⟩ := hg.exists_ball_analyticOnNhd
  refine ⟨r,hr,g,hgr,by simp [g],?_⟩
  have he : ∀ᶠ z : ℂ in Bornology.cobounded ℂ,
      z ≠ 0 ∧ ∀ n ∈ hf.toFinset, z ≠ t n := by
    have h0 : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, z ≠ 0 :=
      Bornology.isBounded_def.mp Bornology.isBounded_singleton
    have ht : ∀ᶠ z : ℂ in Bornology.cobounded ℂ, ∀ n ∈ hf.toFinset, z ≠ t n := by
      rw [Finset.eventually_all]
      intro n _
      exact Bornology.isBounded_def.mp Bornology.isBounded_singleton
    exact h0.and ht
  filter_upwards [he] with z hz
  rw [complex_finiteGap_continued_eq_prod hp hp1 a hf z]
  dsimp only [g]
  congr 1
  apply Finset.prod_congr rfl
  intro n hn
  exact (invertedCriticalFactor_eq (t n) (gap n ^ 2) (c n) z hz.1 (hz.2 n hn)).symm



open NLS.ComplexAnalysis

/-- The exact derivative of the canonical primitive on its original cut domain. -/
theorem complex_primitive_derivative_off_cuts {hp : p ≠ ⊤} {hp1 : 1 < p}
    {W U : Set (CoeffPair p)} (Q : SourceSection19Data hp hp1 W U)
    (a : CoeffPair p) (ha : a ∈ U) (n : ℤ) (z : ℂ)
    (hz : z ∈ sourceCanonicalRootDomain hp hp1 a) :
    deriv (fun w => sourceFullAbelianPrimitive hp hp1 W n (w,a)) z =
      sourceCriticalRootRatioJoint hp hp1 (z,a) := by
  have hd := Q.differential n (z,a) ⟨ha,hz⟩
  rw [deriv_spectral_section_eq_fderiv _ z a hd.differentiableAt, hd.fderiv]
  change (sourceCanonicalRoot hp hp1 a z)⁻¹ *
    (fderiv ℂ (fun u : ℂ × CoeffPair p => canonicalDiscriminant hp
      (periodOnePotential u.2) u.1) (z,a)) (1,0) = _
  rw [← deriv_spectral_section_eq_fderiv _ z a
    (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (z,a) (mem_univ _)).differentiableAt]
  simp only [sourceCriticalRootRatioJoint, div_eq_inv_mul]

/-- At a complex finite-gap source, the derivative of the actual primitive
is the normalized holomorphic inversion germ throughout a full exterior,
including every collapsed tail endpoint. -/
theorem complex_finiteGap_primitive_derivative_germ {hp : p ≠ ⊤} {hp1 : 1 < p}
    {W U V : Set (CoeffPair p)} (Q : SourceSection19Data hp hp1 W U)
    (E : SourceEquation2_15Data hp hp1 V) (a : CoeffPair p)
    (ha : a ∈ U) (haV : a ∈ V) (hf : ComplexFiniteGap hp hp1 a) :
    ∃ R : ℝ, 0 < R ∧ ∃ r : ℝ, 0 < r ∧ r⁻¹ < R ∧ ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball 0 r) ∧ g 0 = -I ∧
      ∀ n : ℤ,
        AnalyticOnNhd ℂ (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,a))
          {z : ℂ | R < ‖z‖} ∧
        ∀ z : ℂ, R < ‖z‖ → HasDerivAt
          (fun w => sourceFullAbelianPrimitive hp hp1 W n (w,a)) (g z⁻¹) z := by
  obtain ⟨T,hT,hcuts⟩ := complex_finiteGap_exterior hp hp1 a hf
  obtain ⟨r,hr,g,hg,hg0,he⟩ := complex_finiteGap_quotient_germ hp hp1 a hf
  obtain ⟨B,_,hB⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.mp he
  let R := max T (max B r⁻¹) + 1
  have hTR : T < R := by dsimp [R]; linarith [le_max_left T (max B r⁻¹)]
  have hBR : B < R := by
    have := (le_max_left B r⁻¹).trans (le_max_right T (max B r⁻¹))
    dsimp [R]; linarith
  have hrR : r⁻¹ < R := by
    have := (le_max_right B r⁻¹).trans (le_max_right T (max B r⁻¹))
    dsimp [R]; linarith
  have hR : 0 < R := hT.trans hTR
  have hgext : AnalyticOnNhd ℂ (fun z => g z⁻¹) {z : ℂ | R < ‖z‖} := by
    intro z hz
    have hzpos := hR.trans hz
    have hi : z⁻¹ ∈ ball (0 : ℂ) r := by
      rw [mem_ball,dist_zero_right,norm_inv]
      exact (inv_lt_comm₀ hzpos hr).mpr (hrR.trans hz)
    exact (hg _ hi).comp (analyticAt_id.inv (norm_pos_iff.mp hzpos))
  refine ⟨R,hR,r,hr,hrR,g,hg,hg0,?_⟩
  intro n
  have hF := (Q.spectral_analytic a ha n).mono (fun z hz => hcuts (hTR.trans hz))
  refine ⟨hF,?_⟩
  have hd : EqOn (deriv (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,a)))
      (fun z => g z⁻¹) {z : ℂ | R < ‖z‖} := by
    apply continuous_eqOn_of_dense_on_open (sourceCanonicalRootDomain hp hp1 a) _
      (dense_sourceCanonicalRootDomain_complex hp hp1 a)
      (isOpen_lt continuous_const continuous_norm) _ _ hF.deriv.continuousOn hgext.continuousOn
    intro z hz
    rw [complex_primitive_derivative_off_cuts Q a ha n z hz.2,
      ← E.continued_eq_quotient a haV z hz.2]
    exact hB (hBR.trans hz.1).le
  intro z hz
  exact (hF z hz).differentiableAt.hasDerivAt.congr_deriv (hd hz)

/-- Single-valuedness eliminates the logarithmic term on the full complex
finite-gap domain. This uses the actual primitive's closed-circle integral. -/
theorem complex_finiteGap_quadratic_derivative {hp : p ≠ ⊤} {hp1 : 1 < p}
    {W U V : Set (CoeffPair p)} (Q : SourceSection19Data hp hp1 W U)
    (E : SourceEquation2_15Data hp hp1 V) (a : CoeffPair p)
    (ha : a ∈ U) (haV : a ∈ V) (hf : ComplexFiniteGap hp hp1 a) :
    ∃ R : ℝ, 0 < R ∧ ∃ r : ℝ, 0 < r ∧ r⁻¹ < R ∧ ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (ball 0 r) ∧ ∀ n : ℤ,
        AnalyticOnNhd ℂ (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,a))
          {z : ℂ | R < ‖z‖} ∧
        ∀ z : ℂ, R < ‖z‖ → HasDerivAt
          (fun w => sourceFullAbelianPrimitive hp hp1 W n (w,a)) (-I+z⁻¹^2*h z⁻¹) z := by
  obtain ⟨R,hR,r,hr,hrR,g,hg,hg0,hF⟩ :=
    complex_finiteGap_primitive_derivative_germ Q E a ha haV hf
  have hgd : deriv g 0 = 0 := by
    let S := R+1
    have hS : 0 < S := by dsimp [S]; linarith
    have hRS : R < S := by dsimp [S]; linarith
    have hSr : S⁻¹ < r := (inv_lt_comm₀ hS hr).mpr (hrR.trans hRS)
    have hzero : (∮ z in C(0,S), g z⁻¹) = 0 := by
      apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt hS.le
      intro z hz
      have hn : ‖z‖ = S := by simpa only [mem_sphere,dist_zero_right] using hz
      exact ((hF 0).2 z (hn ▸ hRS)).hasDerivWithinAt
    have hc := circleIntegral_comp_inv_eq g r S hr hS hSr hg
    rw [hzero] at hc
    have hne : (2*Real.pi*I : ℂ) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
    exact (mul_eq_zero.mp hc.symm).resolve_left hne
  let h := dslope (dslope g 0) 0
  have hh := analyticOnNhd_dslope_zero (dslope g 0) r hr (analyticOnNhd_dslope_zero g r hr hg)
  refine ⟨R,hR,r,hr,hrR,h,hh,?_⟩
  intro n
  refine ⟨(hF n).1,?_⟩
  intro z hz
  have he : g z⁻¹ = -I+z⁻¹^2*h z⁻¹ := by
    rw [eq_second_dslope_expansion g z⁻¹,hg0,hgd,mul_zero,add_zero]
  rw [← he]
  exact (hF n).2 z hz



/-- The actual complex finite-gap primitive has a normalized analytic
inversion remainder. Its zero constant is forced by the collapsed tail
endpoint values, with no real-type assumption. -/
theorem complex_finiteGap_inversion_remainder {hp : p ≠ ⊤} {hp1 : 1 < p}
    {W U V : Set (CoeffPair p)} (Q : SourceSection19Data hp hp1 W U)
    (E : SourceEquation2_15Data hp hp1 V) (a : CoeffPair p)
    (ha : a ∈ U) (haV : a ∈ V) (hf : ComplexFiniteGap hp hp1 a) :
    ∃ R : ℝ, 0 < R ∧ ∃ r : ℝ, 0 < r ∧ r⁻¹ < R ∧ ∃ A : ℂ → ℂ,
      AnalyticOnNhd ℂ A (ball 0 r) ∧ A 0 = 0 ∧
      ∀ z : ℂ, R < ‖z‖ → sourceFullAbelianPrimitive hp hp1 W 0 (z,a) = -I*z+A z⁻¹ := by
  obtain ⟨C,hC⟩ := Q.cauchyFamily a ha
  obtain ⟨R,hR,r,hr,hrR,h,hh,hF⟩ := complex_finiteGap_quadratic_derivative Q E a ha haV hf
  obtain ⟨A,hA,hA0,_,c,heq⟩ := exists_exterior_inversion_remainder
    (fun z => sourceFullAbelianPrimitive hp hp1 W 0 (z,a)) h R r hR hr hrR hh (hF 0).2
  let l : ℤ → ℂ := canonicalPeriodicLeft hp hp1 (periodOnePotential a) (periodOnePotential_mem a)
  have hl := tendsto_sourcePeriodicLeft_norm_atTop hp hp1 a
  have hi : Tendsto (fun n : ℤ => (l n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv₀_cobounded.comp (tendsto_norm_atTop_iff_cobounded.mp hl)
  have hAl : Tendsto (fun n : ℤ => A (l n)⁻¹) atTop (𝓝 0) := by
    simpa only [hA0,Function.comp_def] using! (hA 0 (mem_ball_self hr)).continuousAt.tendsto.comp hi
  have hdisp := (tendsto_sourcePeriodicLeft_sub_free_atTop hp hp1 a).const_mul (-I)
  have ht : Tendsto (fun n : ℤ => -I*(l n-(Real.pi : ℂ)*n)+A (l n)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_add] using hdisp.add hAl
  have hclosed : ∀ᶠ n : ℤ in atTop,
      canonicalPeriodicGap hp hp1 (periodOnePotential a) (periodOnePotential_mem a) n = 0 := by
    have hfin : {n : ℤ | canonicalPeriodicGap hp hp1 (periodOnePotential a) (periodOnePotential_mem a) n ≠ 0}.Finite := hf
    filter_upwards [atTop_le_cofinite hfin.compl_mem_cofinite] with n hn
    exact not_not.mp hn
  have hconst : Tendsto (fun _ : ℤ => -c) atTop (𝓝 (0:ℂ)) := by
    apply ht.congr'
    filter_upwards [hclosed,hl.eventually (eventually_gt_atTop R)] with n hn hln
    have hend := C.fullPrimitive_collapsed_endpoint_value n 0 a hC hn (l n) (by simp [l])
    have he := heq (l n) hln
    simp only [Int.cast_zero,zero_sub,mul_neg] at hend
    rw [hend] at he
    linear_combination -he
  have hc0 : c = 0 := neg_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hconst)
  refine ⟨R,hR,r,hr,hrR,A,hA,hA0,?_⟩
  intro z hz
  simpa only [hc0,add_zero] using heq z hz

/-- A convergent Laurent expansion in every exterior direction for each
complex finite-gap source. Coefficients here are scalar analytic coefficients;
identifying the complete physical hierarchy is a further assertion. -/
theorem complex_finiteGap_laurent {hp : p ≠ ⊤} {hp1 : 1 < p}
    {W U V : Set (CoeffPair p)} (Q : SourceSection19Data hp hp1 W U)
    (E : SourceEquation2_15Data hp hp1 V) (a : CoeffPair p)
    (ha : a ∈ U) (haV : a ∈ V) (hf : ComplexFiniteGap hp hp1 a) :
    ∃ R : ℝ, 0 < R ∧ ∃ c : ℕ → ℂ, ∀ n : ℤ,
      AnalyticOnNhd ℂ (fun z => sourceFullAbelianPrimitive hp hp1 W n (z,a))
        {z : ℂ | R < ‖z‖} ∧
      ∀ z : ℂ, R < ‖z‖ → HasSum (fun k : ℕ => c k*z⁻¹^(k+1))
        (sourceFullAbelianPrimitive hp hp1 W n (z,a)+I*z-I*(Real.pi : ℂ)*n) := by
  obtain ⟨R,hR,r,hr,_,A,hA,hA0,he⟩ := complex_finiteGap_inversion_remainder Q E a ha haV hf
  obtain ⟨c,ε,hε,hc⟩ := exists_hasSum_positive_powers A r hr hA hA0
  obtain ⟨T,_,hT⟩ := complex_finiteGap_exterior hp hp1 a hf
  let S := max R (max T ε⁻¹)
  have hRS : R ≤ S := le_max_left _ _
  have hTS : T ≤ S := (le_max_left _ _).trans (le_max_right _ _)
  have hεS : ε⁻¹ ≤ S := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨S,hR.trans_le hRS,c,?_⟩
  intro n
  refine ⟨(Q.spectral_analytic a ha n).mono (fun z hz => hT (hTS.trans_lt hz)),?_⟩
  intro z hz
  have hv : sourceFullAbelianPrimitive hp hp1 W n (z,a)+I*z-I*(Real.pi : ℂ)*n = A z⁻¹ := by
    rw [Q.index_shift a ha n z (hT (hTS.trans_lt hz)),he z (hRS.trans_lt hz)]
    ring
  rw [hv]
  apply hc
  rw [norm_inv]
  exact (inv_lt_comm₀ (hR.trans (hRS.trans_lt hz)) hε).mpr (hεS.trans_lt hz)

/-- The two common analytic domains used above are constructed before
choosing any complex source. There are no caller-supplied spectral charts. -/
theorem complex_finiteGap_domain (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W U V : Set (CoeffPair p), U ⊆ V ∧
      SourceSection19Data hp hp1 W U ∧ SourceEquation2_15Data hp hp1 V := by
  obtain ⟨V,hV,_,hrV,E⟩ := sourceEquation2_15 hp hp1
  obtain ⟨W,U,hUV,Q⟩ := exists_sourceSection19Data hp hp1 V hV hrV
  exact ⟨W,U,V,hUV,Q,E⟩



/-- The full complex primitive recovers the actual discriminant, including
collapsed endpoints. This is proved from the Floquet multiplier identity. -/
theorem complex_primitive_cosh {hp : p ≠ ⊤} {hp1 : 1 < p}
    {W : Set (CoeffPair p)} {a : CoeffPair p} (D : SourceAbelianSpectralChart hp hp1 W a)
    (hroot : AnalyticOnNhd ℂ (sourceCanonicalRootJointProduct hp hp1)
      (sourceCanonicalRootJointDomain hp hp1 W)) :
    ∀ z ∈ sourceOpenGapComplement hp hp1 a,
      2*cosh (sourceFullAbelianPrimitive hp hp1 W 0 (z,a)) =
        canonicalDiscriminant hp (periodOnePotential a) z := by
  apply continuous_eqOn_of_dense_on_open (sourceCanonicalRootDomain hp hp1 a) _
    (dense_sourceCanonicalRootDomain_complex hp hp1 a)
    (D.discs.isOpen_openGapComplement a D.source_mem) _ _
    (continuousOn_const.mul (continuous_cosh.comp_continuousOn
      (sourceFullAbelianPrimitive_spectral_analytic D 0).continuousOn))
    ((analyticOnNhd_canonicalDiscriminant hp hp1 _ (periodOnePotential_mem a)).continuousOn.mono (subset_univ _))
  intro z hz
  have he := sourceFullAbelianPrimitive_exp D hroot 0 z hz.2
  have hmul := sourceFloquetMultiplier_mul_companion hp hp1 a z hz.2
  have hinv : (sourceFloquetMultiplier hp hp1 a z)⁻¹ =
      (canonicalDiscriminant hp (periodOnePotential a) z-sourceCanonicalRoot hp hp1 a z)/2 :=
    inv_eq_of_mul_eq_one_right hmul
  simp only [Int.cast_zero,mul_zero,exp_zero,one_mul,sourceFloquetJointMultiplier] at he
  change 2*cosh (sourceFullAbelianPrimitive hp hp1 W 0 (z,a)) = _
  rw [two_cosh,exp_neg,he,hinv,sourceFloquetMultiplier]
  ring

/-- One constructed neighborhood supports both the finite-product data
and the actual complex discriminant identity of its primitive. -/
theorem complex_finiteGap_physical_domain (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W U V : Set (CoeffPair p), U ⊆ V ∧
      SourceSection19Data hp hp1 W U ∧ SourceEquation2_15Data hp hp1 V ∧
      ∀ a ∈ U, ∀ z ∈ sourceOpenGapComplement hp hp1 a,
        2*cosh (sourceFullAbelianPrimitive hp hp1 W 0 (z,a)) =
          canonicalDiscriminant hp (periodOnePotential a) z := by
  obtain ⟨V,hV,_,hrV,E⟩ := sourceEquation2_15 hp hp1
  obtain ⟨Wr,Ur,_,hUr,_,hrUr,_,_,hroot,hcharts⟩ :=
    exists_sourceAbelian_almostReal_spectral_charts hp hp1
  obtain ⟨W,U,hU,Q⟩ := exists_sourceSection19Data hp hp1 (V ∩ Ur)
    (hV.inter hUr) (fun a ha => ⟨hrV ha,hrUr ha⟩)
  refine ⟨W,U,V,fun a ha => (hU ha).1,Q,E,?_⟩
  intro a ha z hz
  obtain ⟨D⟩ := Q.charts a ha
  obtain ⟨_,hamem,hD⟩ := hcharts a (hU ha).2
  obtain ⟨Dr,_⟩ := hD a hamem
  rw [sourceFullAbelianPrimitive_independent_neighborhood D Dr 0 z hz]
  exact complex_primitive_cosh Dr hroot z hz

/-- Complex finite-gap Laurent coefficients are physical Riccati
Hamiltonians whenever a smooth periodic representative of the actual
source is supplied. The discriminant comparison is proved from matching
Fourier coefficients, rather than postulated as an asymptotic expansion. -/
theorem complex_finiteGap_smooth_hamiltonians
    {W U V : Set (CoeffPair 2)} (Q : SourceSection19Data (by simp) (by norm_num) W U)
    (E : SourceEquation2_15Data (by simp) (by norm_num) V)
    (hcosh : ∀ a ∈ U, ∀ z ∈ sourceOpenGapComplement (by simp) (by norm_num) a,
      2*cosh (sourceFullAbelianPrimitive (by simp) (by norm_num) W 0 (z,a)) =
        canonicalDiscriminant (by simp) (periodOnePotential a) z)
    (ab : SobolevSource 1) (haU : higherSobolevSourceInclusion 1 ab ∈ U)
    (haV : higherSobolevSourceInclusion 1 ab ∈ V)
    (hf : ComplexFiniteGap (by simp) (by norm_num) (higherSobolevSourceInclusion 1 ab))
    (a b : ℝ → ℂ) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hpa : Function.Periodic a 1) (hpb : Function.Periodic b 1)
    (hca : ∀ j, ab.1.val j = NLS.Fourier.periodOneCoefficient a j)
    (hcb : ∀ j, ab.2.val j = NLS.Fourier.periodOneCoefficient b j) :
    ∃ R : ℝ, 0 < R ∧ ∀ (n : ℤ) (z : ℂ), R < ‖z‖ →
      HasSum (fun k : ℕ => I*classicalNLSHamiltonian a b (k+1)/(2*z)^(k+1))
        (sourceFullAbelianPrimitive (by simp) (by norm_num) W n
          (z,higherSobolevSourceInclusion 1 ab)+I*z-I*(Real.pi : ℂ)*n) := by
  let ψ := higherSobolevSourceInclusion 1 ab
  obtain ⟨R,hR,r,hr,_,A,hA,hA0,hval⟩ :=
    complex_finiteGap_inversion_remainder Q E ψ haU haV hf
  obtain ⟨T,_,hT⟩ := complex_finiteGap_exterior (by simp) (by norm_num) ψ hf
  have htrace (z : ℂ) := (higherSobolev_spectral_functions_eq_classical 1 le_rfl ab a b
    ha.continuous hb.continuous hpa hpb hca hcb z).1
  have he : ∀ᶠ x : ℝ in atTop,
      2*cosh (-I*(x : ℂ)+A (x : ℂ)⁻¹) =
        classicalDiscriminant (classicalPotentialOfFunctions a b ha.continuous hb.continuous) x := by
    filter_upwards [eventually_gt_atTop (max R T)] with x hx
    have hxpos : 0 < x := hR.trans ((le_max_left R T).trans_lt hx)
    have hnorm : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hxpos]
    have hF := hval x (by rw [hnorm]; exact (le_max_left R T).trans_lt hx)
    rw [← hF,← htrace]
    exact hcosh ψ haU x (hT (by change T < ‖(x : ℂ)‖; rw [hnorm]; exact (le_max_right R T).trans_lt hx))
  obtain ⟨S,hS,hs⟩ := exists_nlsHamiltonian_laurent_of_discriminant a b ha hb hpa hpb A
    (hA 0 (mem_ball_self hr)) hA0 he
  refine ⟨max R (max S T),hR.trans_le (le_max_left _ _),?_⟩
  intro n z hz
  have hRz : R < ‖z‖ := (le_max_left _ _).trans_lt hz
  have hSz : S < ‖z‖ := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hz
  have hTz : T < ‖z‖ := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hz
  have hv : sourceFullAbelianPrimitive (by simp) (by norm_num) W n (z,ψ)+I*z-I*(Real.pi : ℂ)*n = A z⁻¹ := by
    rw [Q.index_shift ψ haU n z (hT hTz),hval z hRz]
    ring
  rw [hv]
  exact hs z hSz

end NLS.Articles.DNLSEstimates
