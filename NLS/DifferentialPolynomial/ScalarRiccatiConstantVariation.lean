import NLS.DifferentialPolynomial.RiccatiResolventVariation

/-! # Constant-potential variation of every scalar Hill Riccati coefficient

The coefficient variation is controlled by differentiation in the formal
spectral variable. This supplies the all-order constant-shift relation
without an assumed hierarchy or a list of low-order formulas.
-/
noncomputable section
set_option autoImplicit false
namespace NLS.DifferentialPolynomial
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

/-- Formal degree differentiation: the n-th coefficient is multiplied by n. -/
def powerSeriesDegreeDerivation : Derivation K (PowerSeries A) (PowerSeries A) where
  toFun f := PowerSeries.mk (fun n => (n : A)*PowerSeries.coeff n f)
  map_add' f g := by ext n; simp [mul_add]
  map_smul' c f := by
    ext n
    simp only [PowerSeries.coeff_mk,PowerSeries.coeff_smul]
    simp only [Algebra.smul_def,RingHom.id_apply]
    ring
  map_one_eq_zero' := by
    change PowerSeries.mk (fun n => (n : A)*PowerSeries.coeff n (1 : PowerSeries A)) = 0
    ext n
    simp only [PowerSeries.coeff_mk,PowerSeries.coeff_one]
    split_ifs with hn
    · subst n; simp
    · simp
  leibniz' f g := by
    change PowerSeries.mk (fun n => (n : A)*PowerSeries.coeff n (f*g)) =
      f*PowerSeries.mk (fun n => (n : A)*PowerSeries.coeff n g)+
        g*PowerSeries.mk (fun n => (n : A)*PowerSeries.coeff n f)
    rw [mul_comm g (PowerSeries.mk _)]
    ext n
    simp only [PowerSeries.coeff_mk,PowerSeries.coeff_mul,map_add,Finset.mul_sum]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ij hij
    have he := Finset.mem_antidiagonal.mp hij
    rw [←he,Nat.cast_add]
    ring

@[simp] theorem coeff_powerSeriesDegreeDerivation (R : PowerSeries A) (n : ℕ) :
    PowerSeries.coeff n (powerSeriesDegreeDerivation (K := K) R) = (n : A)*PowerSeries.coeff n R := by
  change PowerSeries.coeff n (PowerSeries.mk (fun j => (j : A)*PowerSeries.coeff j R)) = _
  exact PowerSeries.coeff_mk _ _

@[simp] theorem powerSeriesDegreeDerivation_C (a : A) :
    powerSeriesDegreeDerivation (K := K) (PowerSeries.C a) = 0 := by
  ext n
  simp only [coeff_powerSeriesDegreeDerivation,PowerSeries.coeff_C,map_zero]
  split_ifs with hn
  · subst n; simp
  · simp

@[simp] theorem powerSeriesDegreeDerivation_X :
    powerSeriesDegreeDerivation (K := K) (PowerSeries.X : PowerSeries A) = PowerSeries.X := by
  ext n
  simp only [coeff_powerSeriesDegreeDerivation,PowerSeries.coeff_X]
  split_ifs with hn
  · subst n; simp
  · simp

/-- Coefficient differentiation commutes with the formal degree derivative. -/
theorem powerSeriesDerivation_degree (D : Derivation K A A) (R : PowerSeries A) :
    powerSeriesDerivation D (powerSeriesDegreeDerivation (K := K) R) =
      powerSeriesDegreeDerivation (K := K) (powerSeriesDerivation D R) := by
  ext n
  simp [Derivation.leibniz,smul_eq_mul,Derivation.map_natCast]

/-- The linearized scalar Riccati equation is coefficientwise unique. -/
theorem scalarRiccati_linearized_unique (D : Derivation K A A) (R F G : PowerSeries A)
    (hF : F = -1+powerSeriesDerivation D F*PowerSeries.X+(2*R*F)*PowerSeries.X^2)
    (hG : G = -1+powerSeriesDerivation D G*PowerSeries.X+(2*R*G)*PowerSeries.X^2) : F = G := by
  have hW : F-G = powerSeriesDerivation D (F-G)*PowerSeries.X+(2*R*(F-G))*PowerSeries.X^2 := by
    rw [map_sub]
    linear_combination hF-hG
  have hz (n : ℕ) : PowerSeries.coeff n (F-G) = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases n with _ | _ | n
      · simpa using congrArg (PowerSeries.coeff 0) hW
      · have he := congrArg (PowerSeries.coeff 1) hW
        rw [map_add,PowerSeries.coeff_succ_mul_X,coeff_powerSeriesDerivation,
          ih 0 (by omega),map_zero] at he
        simpa [PowerSeries.coeff_mul_X_pow'] using he
      · have he := congrArg (PowerSeries.coeff (n+2)) hW
        rw [map_add,PowerSeries.coeff_mul_X_pow] at he
        rw [show n+2=(n+1)+1 by omega,PowerSeries.coeff_succ_mul_X] at he
        rw [coeff_powerSeriesDerivation,ih (n+1) (by omega),map_zero,zero_add] at he
        apply he.trans
        rw [PowerSeries.coeff_mul]
        apply Finset.sum_eq_zero
        intro ij hij
        have hij' := Finset.mem_antidiagonal.mp hij
        rw [ih ij.2 (by omega),mul_zero]
  ext n
  exact sub_eq_zero.mp (by simpa only [map_sub] using hz n)

/-- Formal degree differentiation of the scalar Riccati equation. -/
theorem scalarRiccati_formal_degree_equation (D : Derivation K A A) (q : A) :
    powerSeriesDegreeDerivation (K := K) (differentialRiccatiSeries D 1 q) =
      powerSeriesDerivation D (differentialRiccatiSeries D 1 q)*PowerSeries.X+
      powerSeriesDerivation D (powerSeriesDegreeDerivation (K := K) (differentialRiccatiSeries D 1 q))*PowerSeries.X+
      2*(differentialRiccatiSeries D 1 q)^2*PowerSeries.X^2+
      (2*differentialRiccatiSeries D 1 q*powerSeriesDegreeDerivation (K := K) (differentialRiccatiSeries D 1 q))*PowerSeries.X^2 := by
  have he := congrArg (powerSeriesDegreeDerivation (K := K)) (differentialRiccatiSeries_equation D 1 q)
  simp only [map_add,Derivation.leibniz,smul_eq_mul,powerSeriesDegreeDerivation_C,
    powerSeriesDegreeDerivation_X,Derivation.leibniz_pow,map_one,one_mul,zero_add,
    ←powerSeriesDerivation_degree D] at he
  linear_combination he

/-- A commuting perturbation that adds one to the scalar potential has
this exact formal all-order variation. -/
theorem scalarRiccati_constant_variation_series (D E : Derivation K A A)
    (hcomm : ∀ a, E (D a) = D (E a)) (q : A) (hq : E q = 1) :
    powerSeriesDerivation E (differentialRiccatiSeries D 1 q) =
      -1+(PowerSeries.C (-2)*(differentialRiccatiSeries D 1 q+
        powerSeriesDegreeDerivation (K := K) (differentialRiccatiSeries D 1 q)))*PowerSeries.X^2 := by
  let R := differentialRiccatiSeries D 1 q
  have hF : powerSeriesDerivation E R = -1+
      powerSeriesDerivation D (powerSeriesDerivation E R)*PowerSeries.X+
      (2*R*powerSeriesDerivation E R)*PowerSeries.X^2 := by
    have he := differentialRiccatiSeries_linearized D E hcomm 1 q
    simp only [hq,Derivation.map_one_eq_zero,map_one,map_zero,zero_mul,add_zero] at he
    linear_combination he
  apply scalarRiccati_linearized_unique D R _ _ hF
  have hd := scalarRiccati_formal_degree_equation D q
  change powerSeriesDegreeDerivation (K := K) R = _ at hd
  have h2 : powerSeriesDerivation D (2 : PowerSeries A) = 0 := (powerSeriesDerivation D).map_natCast 2
  simp only [map_add,map_neg,Derivation.leibniz,smul_eq_mul,Derivation.leibniz_pow,
    Derivation.map_one_eq_zero,powerSeriesDerivation_X,h2,
    mul_zero,map_neg,map_ofNat]
  linear_combination (-2*PowerSeries.X^2)*hd

/-- The exact triangular coefficient relation for constant-potential variation. -/
theorem scalarRiccati_constant_variation (D E : Derivation K A A)
    (hcomm : ∀ a, E (D a) = D (E a)) (q : A) (hq : E q = 1) (n : ℕ) :
    E (differentialRiccatiSequence D 1 q (n+2)) =
      -2*((n+1 : ℕ) : A)*differentialRiccatiSequence D 1 q n := by
  have he := congrArg (PowerSeries.coeff (n+2)) (scalarRiccati_constant_variation_series D E hcomm q hq)
  rw [coeff_powerSeriesDerivation,coeff_differentialRiccatiSeries,map_add,
    PowerSeries.coeff_mul_X_pow] at he
  simp only [map_neg,neg_mul,PowerSeries.coeff_one,show n+2 ≠ 0 by omega,↓reduceIte,neg_zero,
    zero_add,PowerSeries.coeff_C_mul,map_add,coeff_differentialRiccatiSeries,
    coeff_powerSeriesDegreeDerivation] at he
  rw [he]
  push_cast
  ring

end NLS.DifferentialPolynomial
