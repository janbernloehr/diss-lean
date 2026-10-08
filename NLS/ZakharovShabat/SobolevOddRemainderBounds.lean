import NLS.ZakharovShabat.SobolevOddHamiltonianReal
import NLS.DifferentialPolynomial.RealMonomialBounds

/-! # Physical monomial majorants for the odd Hamiltonian remainder

The finite positive majorant (5.10) is valid pointwise and after integration
for every real H^m source. Every participating multi-index has weight 2m+2
and even total degree, as in (5.9). No interpolation estimate is assumed.
-/
noncomputable section
open NLS.Fourier NLS.DifferentialPolynomial MeasureTheory
open scoped ComplexConjugate
namespace NLS.ZakharovShabat

theorem nlsOddReducedPolynomial_totalWeight (m : ℕ) (hm : 1 ≤ m) :
    (nlsOddReducedPolynomial m hm).IsWeightedHomogeneous totalWeight (2*(m:ℤ)+2) :=
  (Classical.choose_spec (exists_classicalNLSHamiltonian_odd_reduced_polynomial m hm)).2.1

theorem nlsOddReducedPolynomial_fieldCharge (m : ℕ) (hm : 1 ≤ m) :
    (nlsOddReducedPolynomial m hm).IsWeightedHomogeneous fieldCharge 0 :=
  (Classical.choose_spec (exists_classicalNLSHamiltonian_odd_reduced_polynomial m hm)).2.2.1

/-- Every actual remainder monomial satisfies both multi-index restrictions (5.9). -/
theorem nlsOddReducedPolynomial_multiplicity_constraints (m : ℕ) (hm : 1 ≤ m)
    (d : Monomial) (hd : d ∈ (nlsOddReducedPolynomial m hm).support) :
    (∑ k ∈ Finset.range m, (k+1)*jetMultiplicity d k) = 2*m+2 ∧
      Even (∑ k ∈ Finset.range m, jetMultiplicity d k) := by
  have ho (v : Jet) (hv : v ∈ d.support) : v.2 < m := by
    have := nlsOddReducedPolynomial_order m hm d hd v hv
    omega
  have hw := nlsOddReducedPolynomial_totalWeight m hm (MvPolynomial.mem_support_iff.mp hd)
  rw [← jetMultiplicity_weight m d ho] at hw
  exact ⟨by exact_mod_cast hw,jetMultiplicity_even m d ho
    (nlsOddReducedPolynomial_fieldCharge m hm (MvPolynomial.mem_support_iff.mp hd))⟩

/-- The remainder has at least four fields in every monomial; its total field
count is at most 2m+2. These are the nonlinear exponents needed for interpolation. -/
theorem nlsOddReducedPolynomial_field_degree_bounds (m : ℕ) (hm : 1 ≤ m)
    (d : Monomial) (hd : d ∈ (nlsOddReducedPolynomial m hm).support) :
    4 ≤ (∑ k ∈ Finset.range m, jetMultiplicity d k) ∧
      (∑ k ∈ Finset.range m, jetMultiplicity d k) ≤ 2*m+2 := by
  obtain ⟨hw,he⟩ := nlsOddReducedPolynomial_multiplicity_constraints m hm d hd
  have hu : (∑ k ∈ Finset.range m, jetMultiplicity d k) ≤ 2*m+2 := by
    rw [← hw]
    apply Finset.sum_le_sum
    intro k _
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hl : 2*m+2 ≤ m*(∑ k ∈ Finset.range m, jetMultiplicity d k) := by
    rw [← hw,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    exact Nat.mul_le_mul_right _ (by have := Finset.mem_range.mp hk; omega)
  refine ⟨?_,hu⟩
  obtain ⟨c,hc⟩ := he
  by_contra h
  have htwo : (∑ k ∈ Finset.range m, jetMultiplicity d k) ≤ 2 := by omega
  have := Nat.mul_le_mul_left m htwo
  omega

/-- The two fields of every lower real jet have equal pointwise norm. -/
theorem lowerSobolevJet_real_norm (m k : ℕ) (a : realTypeHigherSobolevSourceLocus m) (x : ℝ) :
    ‖lowerSobolevJet m (true,k) a.val (x : AddCircle (2:ℝ))‖ =
      ‖lowerSobolevJet m (false,k) a.val (x : AddCircle (2:ℝ))‖ := by
  by_cases hk : k < m
  · simp only [lowerSobolevJet,hk,↓reduceDIte,↓reduceIte,Bool.false_eq_true,
      ContinuousLinearMap.comp_apply]
    change ‖hierarchySobolevJetContinuous m k hk a.val.2 (x : AddCircle (2:ℝ))‖ =
      ‖hierarchySobolevJetContinuous m k hk a.val.1 (x : AddCircle (2:ℝ))‖
    rw [hierarchySobolevJetContinuous_real m k hk a.val.1 a.val.2
      (realTypeHigherSobolevSource_coefficients m a),Complex.norm_conj]
  · simp [lowerSobolevJet,hk]

/-- One real monomial magnitude, combining conjugate factors at each order. -/
def sobolevRealMonomial (m : ℕ) (d : Monomial) (a : SobolevSource m) (x : ℝ) : ℝ :=
  ∏ k ∈ Finset.range m, ‖lowerSobolevJet m (false,k) a (x : AddCircle (2:ℝ))‖^jetMultiplicity d k

/-- The explicit positive polynomial majorant from (5.10). -/
def sobolevOddRemainderMajorant (m : ℕ) (hm : 1 ≤ m) (a : SobolevSource m) (x : ℝ) : ℝ :=
  ∑ d ∈ (nlsOddReducedPolynomial m hm).support,
    ‖(nlsOddReducedPolynomial m hm).coeff d‖ * sobolevRealMonomial m d a x

theorem continuous_sobolevRealMonomial (m : ℕ) (d : Monomial) (a : SobolevSource m) :
    Continuous (sobolevRealMonomial m d a) := by
  unfold sobolevRealMonomial
  fun_prop

theorem continuous_sobolevOddRemainderMajorant (m : ℕ) (hm : 1 ≤ m) (a : SobolevSource m) :
    Continuous (sobolevOddRemainderMajorant m hm a) := by
  unfold sobolevOddRemainderMajorant
  exact continuous_finsetSum _ fun d _ => continuous_const.mul (continuous_sobolevRealMonomial m d a)

/-- Equation (5.10) for arbitrary real H^m sources, pointwise on the physical interval. -/
theorem norm_sobolevOddRemainderField_le (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) (x : ℝ) :
    ‖sobolevPolynomialField m (nlsOddReducedPolynomial m hm) a.val (x : AddCircle (2:ℝ))‖ ≤
      sobolevOddRemainderMajorant m hm a.val x := by
  rw [sobolevPolynomialField_apply]
  exact norm_eval_le_real_monomials m hm _ (nlsOddReducedPolynomial_order m hm) _
    (fun k => lowerSobolevJet_real_norm m k a x)

/-- The remainder mean is bounded by the integrated positive monomial majorant. -/
theorem norm_sobolevOddRemainderMean_le_integral (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    ‖sobolevPolynomialMean m (nlsOddReducedPolynomial m hm) a.val‖ ≤
      ∫ x in (0:ℝ)..1, sobolevOddRemainderMajorant m hm a.val x := by
  rw [sobolevPolynomialMean_eq_physical_integral]
  apply (intervalIntegral.norm_integral_le_integral_norm (by norm_num)).trans
  apply intervalIntegral.integral_mono_on (by norm_num)
  · exact ((sobolevPolynomialField m (nlsOddReducedPolynomial m hm) a.val).continuous.comp
      continuous_quotient_mk').norm.intervalIntegrable 0 1
  · exact (continuous_sobolevOddRemainderMajorant m hm a.val).intervalIntegrable 0 1
  · intro x _
    exact norm_sobolevOddRemainderField_le m hm a x

/-- The integrated majorant is exactly the finite sum used for monomial-by-monomial estimates. -/
theorem integral_sobolevOddRemainderMajorant (m : ℕ) (hm : 1 ≤ m) (a : SobolevSource m) :
    (∫ x in (0:ℝ)..1, sobolevOddRemainderMajorant m hm a x) =
      ∑ d ∈ (nlsOddReducedPolynomial m hm).support,
        ‖(nlsOddReducedPolynomial m hm).coeff d‖ * ∫ x in (0:ℝ)..1, sobolevRealMonomial m d a x := by
  unfold sobolevOddRemainderMajorant
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro d _
    exact intervalIntegral.integral_const_mul _ _
  · intro d _
    exact (continuous_const.mul (continuous_sobolevRealMonomial m d a)).intervalIntegrable 0 1

/-- The deviation of the Hamiltonian from its leading squared derivative norm
is controlled by the concrete monomial integrals, prior to interpolation. -/
theorem abs_sobolevOddHamiltonian_sub_kinetic_le (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) :
    |(sobolevOddHamiltonian m hm a.val).re-‖hierarchySobolevJetL2 m m le_rfl a.val.1‖^2| ≤
      ∑ d ∈ (nlsOddReducedPolynomial m hm).support,
        ‖(nlsOddReducedPolynomial m hm).coeff d‖ * ∫ x in (0:ℝ)..1, sobolevRealMonomial m d a.val x := by
  rw [sobolevOddHamiltonian_real_decomposition,Complex.add_re,Complex.ofReal_re,add_sub_cancel_left]
  exact (Complex.abs_re_le_norm _).trans
    ((norm_sobolevOddRemainderMean_le_integral m hm a).trans_eq
      (integral_sobolevOddRemainderMajorant m hm a.val))

end NLS.ZakharovShabat
