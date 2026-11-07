import NLS.Articles.DNLSEstimates.ComplexFiniteGap
import NLS.Articles.DNLSEstimates.HigherActions
import NLS.ComplexAnalysis.FiniteCircleHoleDecomposition
import NLS.ComplexAnalysis.PolynomialInversionCircleCoefficients

/-!
# A spectral extension of the physical finite-gap Hamiltonians

The physical Riccati Hamiltonians keep their independent weak-derivative
and Fourier-mean definitions. On rough complex finite-gap sources, this
module constructs a spectral extension from the original action contours,
proves agreement on every physical Sobolev domain, and identifies its
coefficients in the independently normalized Laurent expansion.
-/
noncomputable section
open Set Complex Metric Filter Topology NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.Articles.DNLSEstimates
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A common Cauchy family supplies actual original isolating circles
at the smaller radii. -/
def finiteGapPeriodCircle {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (a : CoeffPair p)
    (ha : a ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ) :
    SourceCriticalRootPeriodCircle hp hp1 a n where
  center := (C.discs.center n).re
  radius := C.discs.inner n
  radius_pos := C.discs.inner_pos n
  gap := by
    have hc (j : ℤ) : ((C.discs.center j).re : ℂ) = C.discs.center j := by
      apply Complex.ext <;> simp [C.discs.center_real]
    rw [hc]
    exact C.discs.segment_subset a ha n
  other := by
    intro m hm w hw
    have hc (j : ℤ) : ((C.discs.center j).re : ℂ) = C.discs.center j := by
      apply Complex.ext <;> simp [C.discs.center_real]
    apply re_separated_of_disjoint_realCenteredBalls
      (a := (C.discs.center n).re) (b := (C.discs.center m).re)
      (C.discs.inner_pos n) (C.discs.inner_pos m)
    · rw [hc,hc]
      exact (C.discs.disjoint n m hm.symm).mono
        (ball_subset_ball (C.discs.inner_lt n).le) (ball_subset_ball (C.discs.inner_lt m).le)
    · rw [hc]
      exact C.discs.segment_subset a ha m hw

/-- The original higher actions are absolutely summable at every finite
gap source, without a source Sobolev assumption. -/
theorem finiteGap_higherActions_sum {hp : p ≠ ⊤} {hp1 : 1 < p}
    {W U : Set (CoeffPair p)} (Q : SourceSection19Data hp hp1 W U)
    (a : CoeffPair p) (ha : a ∈ U) (hf : ComplexFiniteGap hp hp1 a) (k : ℕ) :
    Summable (fun n : ℤ => ‖sourceIndexedHigherAction hp hp1 n k a‖) ∧
      (∑' n : ℤ, sourceIndexedHigherAction hp hp1 n k a) =
        ∑ n ∈ hf.toFinset, sourceIndexedHigherAction hp hp1 n k a := by
  classical
  have hz (n : ℤ) (hn : n ∉ hf.toFinset) : sourceIndexedHigherAction hp hp1 n k a = 0 := by
    apply Q.indexedHigherAction_of_collapsed a ha n k
    by_contra hg
    exact hn (hf.mem_toFinset.mpr hg)
  exact ⟨summable_of_ne_finset_zero (s := hf.toFinset) (fun n hn => by rw [hz n hn,norm_zero]),
    tsum_eq_sum hz⟩

/-- The spectral extension, in the library's calibrated physical phase.
This finite trace is defined independently of any Laurent coefficients. -/
def finiteGapHamiltonianExtension (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : CoeffPair p) (hf : ComplexFiniteGap hp hp1 a) (order : ℕ) : ℂ :=
  2^(order-1) * ∑ n ∈ hf.toFinset, sourceIndexedHigherAction hp hp1 n (order-1) a

/-- Where the independently defined physical Hamiltonian exists, the
spectral extension has exactly that value, including complex inputs. -/
theorem finiteGapHamiltonianExtension_eq_physical {W U : Set (CoeffPair 2)}
    (Q : SourceSection19Data (by simp) (by norm_num) W U) (s k : ℕ) (hk : k ≤ s)
    (a : SobolevSource s) (ha : higherSobolevSourceInclusion s a ∈ U)
    (hf : ComplexFiniteGap (by simp) (by norm_num) (higherSobolevSourceInclusion s a)) :
    finiteGapHamiltonianExtension (by simp) (by norm_num) (higherSobolevSourceInclusion s a) hf (k+1) =
      sobolevNLSHamiltonian s a (k+1) (by omega) := by
  rw [finiteGapHamiltonianExtension,Nat.add_sub_cancel,
    ← (finiteGap_higherActions_sum Q _ ha hf k).2,Q.indexedHigherAction_hamiltonian_trace s k hk a ha]
  exact mul_div_cancel₀ _ (pow_ne_zero k (by norm_num : (2 : ℂ) ≠ 0))

/-- The finite trace equals the actual exterior primitive contour for
all powers. The same exterior threshold works at every order. -/
theorem finiteGap_trace_exterior_contour {hp : p ≠ ⊤} {hp1 : 1 < p}
    {W U : Set (CoeffPair p)} (Q : SourceSection19Data hp hp1 W U)
    (a : CoeffPair p) (ha : a ∈ U) (hf : ComplexFiniteGap hp hp1 a) :
    ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R → ∀ k : ℕ,
      (∑ n ∈ hf.toFinset, sourceIndexedHigherAction hp hp1 n k a) =
        -(Real.pi : ℂ)⁻¹ * ∮ z in C(0,R), z^k*sourceFullAbelianPrimitive hp hp1 W 0 (z,a) := by
  classical
  obtain ⟨C,hC⟩ := Q.cauchyFamily a ha
  let s := hf.toFinset
  let r := C.discs.inner
  let c := C.discs.center
  let t : ℤ → ℝ := fun n => (C.discs.inner n+C.discs.outer n)/2
  have hrt (n : ℤ) : r n < t n := by dsimp [r,t]; linarith [C.discs.inner_lt n]
  have hto (n : ℤ) : t n < C.discs.outer n := by dsimp [t]; linarith [C.discs.inner_lt n]
  have hc : IsCompact (⋃ n ∈ s, closedBall (c n) (t n)) :=
    s.finite_toSet.isCompact_biUnion fun n _ => isCompact_closedBall _ _
  obtain ⟨B,hB⟩ := hc.isBounded.exists_norm_le
  let T := max B 0+1
  have hT : 0 < T := by dsimp [T]; positivity
  refine ⟨T,hT,?_⟩
  intro R hR k
  have hRp : 0 < R := hT.trans_le hR
  have henclosed (n : ℤ) (hn : n ∈ s) : closedBall (c n) (t n) ⊆ ball 0 R := by
    intro z hz
    have hb := hB z (mem_iUnion₂.mpr ⟨n,hn,hz⟩)
    rw [mem_ball,dist_zero_right]
    have hBT : B < T := by dsimp [T]; linarith [le_max_left B 0]
    exact (hb.trans_lt hBT).trans_le hR
  have hdisj (n : ℤ) (_hn : n ∈ s) (m : ℤ) (_hm : m ∈ s) (hnm : n ≠ m) :
      Disjoint (closedBall (c n) (t n)) (closedBall (c m) (t m)) :=
    (C.discs.disjoint n m hnm).mono (closedBall_subset_ball (hto n)) (closedBall_subset_ball (hto m))
  have hF : AnalyticOnNhd ℂ (fun z => z^k*sourceFullAbelianPrimitive hp hp1 W 0 (z,a))
      (circleHoleDomain 0 R s c r) := by
    intro z hz
    apply (analyticAt_id.pow k).mul
    apply Q.spectral_analytic a ha 0 z
    intro n hn hzn
    have hns : n ∈ s := hf.mem_toFinset.mpr hn
    exact hz.2 n hns (C.discs.segment_subset a hC n hzn)
  have hdec := circleIntegral_eq_sum_of_finite_holes 0 R hRp.le s c r t
    (fun z => z^k*sourceFullAbelianPrimitive hp hp1 W 0 (z,a))
    (fun n _ => C.discs.inner_pos n) (fun n _ => hrt n) henclosed hdisj hF
  rw [hdec,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  obtain ⟨D⟩ := Q.charts a ha
  have hc' : ((C.discs.center n).re : ℂ) = C.discs.center n := by
    apply Complex.ext <;> simp [C.discs.center_real]
  simpa only [finiteGapPeriodCircle,hc'] using
    sourceIndexedHigherAction_eq_primitive (finiteGapPeriodCircle C a hC n) D k 0



/-- An exterior inversion germ gives the exact polynomial contour moment,
without interchanging an infinite Laurent sum and a contour integral. -/
theorem inversionPrimitive_circle_coefficient (F A : ℂ → ℂ) (S r R : ℝ)
    (hr : 0 < r) (hR : 0 < R) (hSR : S < R) (hRr : R⁻¹ < r)
    (hA : AnalyticOnNhd ℂ A (ball 0 r))
    (he : ∀ z : ℂ, S < ‖z‖ → F z = -I*z+A z⁻¹) (k : ℕ) :
    (∮ z in C(0,R), z^k*F z) =
      (2*Real.pi*I : ℂ)*(iteratedDeriv (k+1) A 0/(k+1).factorial) := by
  have hgi : CircleIntegrable (fun z : ℂ => z^k*A z⁻¹) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    have hn : ‖z‖ = R := by simpa only [mem_sphere,dist_zero_right] using hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hn.symm ▸ hR)
    have hw : z⁻¹ ∈ ball (0 : ℂ) r := by simpa only [mem_ball,dist_zero_right,norm_inv,hn] using hRr
    exact ((continuousAt_id.fun_pow k).fun_mul ((hA z⁻¹ hw).continuousAt.comp
      (f := fun z : ℂ => z⁻¹) (continuousAt_inv₀ hz0))).continuousWithinAt
  have hpoly : Differentiable ℂ (fun z : ℂ => z^k*(-I*z)) := by intro z; fun_prop
  have hzero : (∮ z in C(0,R), z^k*(-I*z)) = 0 :=
    (DiffContOnCl.mk_ball hpoly.differentiableOn hpoly.continuous.continuousOn).circleIntegral_eq_zero hR.le
  calc
    _ = ∮ z in C(0,R), z^k*(-I*z)+z^k*A z⁻¹ := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      have hn : ‖z‖ = R := by simpa only [mem_sphere,dist_zero_right] using hz
      dsimp only
      rw [he z (hn.symm ▸ hSR),mul_add]
    _ = _ := by
      rw [circleIntegral.integral_add (hpoly.continuous.continuousOn.circleIntegrable hR.le) hgi,
        hzero,zero_add,circleIntegral_pow_mul_comp_inv_eq A r R hr hR hRr hA k]

/-- All coefficients of the actual complex finite-gap inversion germ are
the independent finite contour traces. The trace is not defined from this germ. -/
theorem complex_finiteGap_extended_hamiltonian_inversion {hp : p ≠ ⊤} {hp1 : 1 < p}
    {W U V : Set (CoeffPair p)} (Q : SourceSection19Data hp hp1 W U)
    (E : SourceEquation2_15Data hp hp1 V) (a : CoeffPair p)
    (ha : a ∈ U) (haV : a ∈ V) (hf : ComplexFiniteGap hp hp1 a) :
    ∃ R : ℝ, 0 < R ∧ ∃ A : ℂ → ℂ, AnalyticAt ℂ A 0 ∧ A 0 = 0 ∧
      (∀ k : ℕ, iteratedDeriv (k+1) A 0/(k+1).factorial =
        I*finiteGapHamiltonianExtension hp hp1 a hf (k+1)/2^(k+1)) ∧
      ∀ z : ℂ, R < ‖z‖ → sourceFullAbelianPrimitive hp hp1 W 0 (z,a) = -I*z+A z⁻¹ := by
  obtain ⟨R,hR,r,hr,hrR,A,hA,hA0,he⟩ := complex_finiteGap_inversion_remainder Q E a ha haV hf
  obtain ⟨T,_,hT⟩ := finiteGap_trace_exterior_contour Q a ha hf
  let S := max R T+1
  have hRS : R < S := by dsimp [S]; linarith [le_max_left R T]
  have hTS : T ≤ S := by dsimp [S]; linarith [le_max_right R T]
  have hS : 0 < S := hR.trans hRS
  refine ⟨R,hR,A,hA 0 (mem_ball_self hr),hA0,?_,he⟩
  intro k
  have hc := inversionPrimitive_circle_coefficient
    (fun z => sourceFullAbelianPrimitive hp hp1 W 0 (z,a)) A R r S hr hS hRS
    ((inv_lt_comm₀ hS hr).mpr (hrR.trans hRS)) hA he k
  have ht := hT S hTS k
  rw [hc] at ht
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [finiteGapHamiltonianExtension,Nat.add_sub_cancel,pow_succ]
  rw [ht]
  field_simp
  ring_nf
  simp only [I_sq]
  ring

/-- The nonsmooth spectral Hamiltonian extension supplies a genuinely
convergent all-order Laurent series for the actual primitive. -/
theorem complex_finiteGap_extended_hamiltonian_laurent {hp : p ≠ ⊤} {hp1 : 1 < p}
    {W U V : Set (CoeffPair p)} (Q : SourceSection19Data hp hp1 W U)
    (E : SourceEquation2_15Data hp hp1 V) (a : CoeffPair p)
    (ha : a ∈ U) (haV : a ∈ V) (hf : ComplexFiniteGap hp hp1 a) :
    ∃ R : ℝ, 0 < R ∧ ∀ (n : ℤ) (z : ℂ), R < ‖z‖ →
      HasSum (fun k : ℕ => I*finiteGapHamiltonianExtension hp hp1 a hf (k+1)/(2*z)^(k+1))
        (sourceFullAbelianPrimitive hp hp1 W n (z,a)+I*z-I*(Real.pi : ℂ)*n) := by
  obtain ⟨R,hR,A,hA,hA0,hcoeff,he⟩ := complex_finiteGap_extended_hamiltonian_inversion Q E a ha haV hf
  have hs := hasFPowerSeriesAt_iff.mp hA.hasFPowerSeriesAt
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hs
  have hseries (w : ℂ) (hw : ‖w‖ < ε) : HasSum
      (fun k : ℕ => (I*finiteGapHamiltonianExtension hp hp1 a hf (k+1)/2^(k+1))*w^(k+1)) (A w) := by
    have hsum := hball (show w ∈ ball (0 : ℂ) ε by simpa only [mem_ball,dist_zero_right] using hw)
    simp only [FormalMultilinearSeries.coeff_ofScalars,smul_eq_mul,zero_add] at hsum
    have htail := (hasSum_nat_add_iff' 1).mpr hsum
    simpa only [hcoeff,Finset.sum_range_one,iteratedDeriv_zero,hA0,zero_div,mul_zero,zero_mul,
      sub_zero,mul_comm] using htail
  obtain ⟨T,_,hT⟩ := complex_finiteGap_exterior hp hp1 a hf
  let S := max R (max T ε⁻¹)
  have hRS : R ≤ S := le_max_left _ _
  have hTS : T ≤ S := (le_max_left _ _).trans (le_max_right _ _)
  have hεS : ε⁻¹ ≤ S := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨S,hR.trans_le hRS,?_⟩
  intro n z hz
  have hv : sourceFullAbelianPrimitive hp hp1 W n (z,a)+I*z-I*(Real.pi : ℂ)*n = A z⁻¹ := by
    rw [Q.index_shift a ha n z (hT (hTS.trans_lt hz)),he z (hRS.trans_lt hz)]
    ring
  rw [hv]
  have hw : ‖z⁻¹‖ < ε := by
    rw [norm_inv]
    exact (inv_lt_comm₀ (hR.trans (hRS.trans_lt hz)) hε).mpr (hεS.trans_lt hz)
  convert hseries z⁻¹ hw using 1
  ext k
  rw [mul_pow,div_mul_eq_div_div,div_eq_mul_inv,inv_pow]

/-- The article phase, with positive mass at order one and the raw Riccati
phase at every higher order. This extends the physical hierarchy only on
the finite-gap locus; no differentiability is attributed to rough sources. -/
def finiteGapArticleHamiltonian (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : CoeffPair p) (hf : ComplexFiniteGap hp hp1 a) (order : ℕ) : ℂ :=
  if order = 1 then finiteGapHamiltonianExtension hp hp1 a hf 1
  else I^(order+1)*finiteGapHamiltonianExtension hp hp1 a hf order

/-- The extension agrees with the independently defined physical Riccati
mean throughout its complex Sobolev domain, in the article's phase. -/
theorem finiteGapArticleHamiltonian_eq_hierarchy {W U : Set (CoeffPair 2)}
    (Q : SourceSection19Data (by simp) (by norm_num) W U) (s k : ℕ) (hk : k ≤ s)
    (a : SobolevSource s) (ha : higherSobolevSourceInclusion s a ∈ U)
    (hf : ComplexFiniteGap (by simp) (by norm_num) (higherSobolevSourceInclusion s a)) :
    finiteGapArticleHamiltonian (by simp) (by norm_num) (higherSobolevSourceInclusion s a) hf (k+1) =
      hierarchyHamiltonian s k hk a := by
  by_cases h : k = 0
  · subst k
    simp only [finiteGapArticleHamiltonian, Nat.zero_add, ↓reduceIte, hierarchyHamiltonian]
    exact finiteGapHamiltonianExtension_eq_physical Q s 0 hk a ha hf
  · rw [finiteGapArticleHamiltonian, if_neg (by omega : k+1 ≠ 1),
      finiteGapHamiltonianExtension_eq_physical Q s k hk a ha hf,
      sobolevNLSHamiltonian_succ_eq_tsum s k hk, hierarchyHamiltonian, if_neg h]
    have hphase : I^(k+2)*(-I)^(k+2) = (1 : ℂ) := by
      rw [← mul_pow]
      norm_num [I_sq]
    simp only [Nat.add_assoc, ← mul_assoc, hphase, one_mul]

/-- Coefficient conversion keeps the exceptional minus sign on H1 and
the printed powers of 2i at every subsequent order. -/
theorem finiteGapArticleHamiltonian_coefficient (hp : p ≠ ⊤) (hp1 : 1 < p)
    (a : CoeffPair p) (hf : ComplexFiniteGap hp hp1 a) (k : ℕ) (z : ℂ) :
    I*finiteGapHamiltonianExtension hp hp1 a hf (k+1)/(2*z)^(k+1) =
      if k = 0 then -finiteGapArticleHamiltonian hp hp1 a hf 1/(2*I*z)
      else finiteGapArticleHamiltonian hp hp1 a hf (k+1)/(2*I*z)^(k+1) := by
  by_cases h : k = 0
  · subst k
    simp only [Nat.zero_add, pow_one, ↓reduceIte, finiteGapArticleHamiltonian]
    simp only [div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
    ring
  · rw [if_neg h, finiteGapArticleHamiltonian, if_neg (by omega : k+1 ≠ 1)]
    have hphase : I^(k+2)*(-I)^(k+1) = I := by
      rw [show k+2 = (k+1)+1 by omega, pow_succ]
      calc
        _ = (I*(-I))^(k+1)*I := by rw [mul_pow]; ring
        _ = I := by norm_num [I_sq]
    simp only [mul_pow, div_eq_mul_inv, mul_inv_rev, ← inv_pow, Complex.inv_I]
    calc
      _ = (I^(k+2)*(-I)^(k+1))*finiteGapHamiltonianExtension hp hp1 a hf (k+1)*
        ((2 : ℂ)⁻¹)^(k+1)*(z⁻¹)^(k+1) := by rw [hphase]; ring
      _ = _ := by ring

/-- The complete complex finite-gap Laurent expansion on constructed
common domains, with independently defined finite action traces at rough
sources. Physical Riccati agreement is the preceding theorem. -/
theorem exists_complex_finiteGap_extended_hamiltonian_domain (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W U : Set (CoeffPair p), SourceSection19Data hp hp1 W U ∧
      ∀ a : CoeffPair p, a ∈ U → ∀ hf : ComplexFiniteGap hp hp1 a,
        ∃ R : ℝ, 0 < R ∧ ∀ (n : ℤ) (z : ℂ), R < ‖z‖ →
          HasSum (fun k : ℕ => if k = 0 then -finiteGapArticleHamiltonian hp hp1 a hf 1/(2*I*z)
            else finiteGapArticleHamiltonian hp hp1 a hf (k+1)/(2*I*z)^(k+1))
            (sourceFullAbelianPrimitive hp hp1 W n (z,a)+I*z-I*(Real.pi : ℂ)*n) := by
  obtain ⟨W,U,V,hUV,Q,E⟩ := complex_finiteGap_domain hp hp1
  refine ⟨W,U,Q,?_⟩
  intro a ha hf
  obtain ⟨R,hR,he⟩ := complex_finiteGap_extended_hamiltonian_laurent Q E a ha (hUV ha) hf
  refine ⟨R,hR,?_⟩
  intro n z hz
  simpa only [finiteGapArticleHamiltonian_coefficient] using he n z hz

/-- At odd order 2m+1, integration by parts defines the independent
physical Hamiltonian already on complex H^m. The rough spectral extension
agrees on that sharp domain as well. -/
theorem finiteGapHamiltonianExtension_eq_odd_physical {W U : Set (CoeffPair 2)}
    (Q : SourceSection19Data (by simp) (by norm_num) W U) (m : ℕ) (hm : 1 ≤ m)
    (a : SobolevSource m) (ha : higherSobolevSourceInclusion m a ∈ U)
    (hf : ComplexFiniteGap (by simp) (by norm_num) (higherSobolevSourceInclusion m a)) :
    finiteGapHamiltonianExtension (by simp) (by norm_num) (higherSobolevSourceInclusion m a) hf (2*m+1) =
      sobolevOddHamiltonian m hm a := by
  rw [finiteGapHamiltonianExtension,Nat.add_sub_cancel,
    ← (finiteGap_higherActions_sum Q _ ha hf (2*m)).2,Q.indexedHigherAction_oddHamiltonian_trace m hm a ha]
  have hpow : (2 : ℂ)^(2*m) = (4 : ℂ)^m := by rw [pow_mul]; norm_num
  rw [hpow]
  exact mul_div_cancel₀ _ (pow_ne_zero m (by norm_num : (4 : ℂ) ≠ 0))
end NLS.Articles.DNLSEstimates
