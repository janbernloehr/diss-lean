import NLS.ZakharovShabat.SourceCorollary13_2Regular

/-! # Literal Fourier formulas for the full canonical angle brackets

These formulas use the original complex angle and action derivatives.
The sums converge absolutely, including below exponent two. Frequency
reversal and the physical Poisson sign `-i` are explicit.
-/

noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

theorem thetaTheta_pairing_summable_norm
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    let L := sourceAngularThetaDifferential hp hp1 n s φ.val
    let M := sourceAngularThetaDifferential hp hp1 m s φ.val
    Summable (fun k : ℤ => ‖L (CoeffPair.inlCLM (lp.single p k 1)) *
      M (CoeffPair.inrCLM (lp.single p (-k) 1)) - L (CoeffPair.inrCLM (lp.single p k 1)) *
        M (CoeffPair.inlCLM (lp.single p (-k) 1))‖) := by
  simpa only [thetaRegularCotangent_toCotangent] using
    (D.thetaRegularCotangent n φ hn).summable_norm (D.thetaRegularCotangent m φ hm)

theorem thetaTheta_fourier_bracket_eq_zero
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    let L := sourceAngularThetaDifferential hp hp1 n s φ.val
    let M := sourceAngularThetaDifferential hp hp1 m s φ.val;
    -I * (∑' k : ℤ, (L (CoeffPair.inlCLM (lp.single p k 1)) *
      M (CoeffPair.inrCLM (lp.single p (-k) 1)) - L (CoeffPair.inrCLM (lp.single p k 1)) *
        M (CoeffPair.inlCLM (lp.single p (-k) 1)))) = 0 := by
  have h := (D.thetaRegularCotangent n φ hn).bivector_eq_tsum (D.thetaRegularCotangent m φ hm)
  rw [D.thetaRegularCotangent_bivector_eq_zero n m φ hn hm] at h
  simpa only [thetaRegularCotangent_toCotangent] using h.symm

theorem thetaAction_pairing_summable_norm
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    let L := sourceAngularThetaDifferential hp hp1 n s φ.val
    let M := fderiv ℂ (sourceComplexAction hp hp1 m) φ.val
    Summable (fun k : ℤ => ‖L (CoeffPair.inlCLM (lp.single p k 1)) *
      M (CoeffPair.inrCLM (lp.single p (-k) 1)) - L (CoeffPair.inrCLM (lp.single p k 1)) *
        M (CoeffPair.inlCLM (lp.single p (-k) 1))‖) := by
  simpa only [thetaRegularCotangent_toCotangent, sourceActionRegularCotangent_toCotangent] using
    (D.thetaRegularCotangent n φ hn).summable_norm (sourceActionRegularCotangent hp hp1 m φ)

theorem thetaAction_fourier_bracket_eq_kronecker
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0) :
    let L := sourceAngularThetaDifferential hp hp1 n s φ.val
    let M := fderiv ℂ (sourceComplexAction hp hp1 m) φ.val;
    -I * (∑' k : ℤ, (L (CoeffPair.inlCLM (lp.single p k 1)) *
      M (CoeffPair.inrCLM (lp.single p (-k) 1)) - L (CoeffPair.inrCLM (lp.single p k 1)) *
        M (CoeffPair.inlCLM (lp.single p (-k) 1)))) = if n = m then 1 else 0 := by
  have h := (D.thetaRegularCotangent n φ hn).bivector_eq_tsum (sourceActionRegularCotangent hp hp1 m φ)
  rw [D.thetaActionRegular_bivector_eq_kronecker n m φ hn] at h
  simpa only [thetaRegularCotangent_toCotangent, sourceActionRegularCotangent_toCotangent] using h.symm

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
