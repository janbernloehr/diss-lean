import NLS.ZakharovShabat.SourceAngularThetaThetaDiscriminantGapZeros
import NLS.ZakharovShabat.SourcePsiVariationCombinationInterpolation

/-! # Actual discriminant stationarity of the angle/angle bracket

The entire spectral variation is an actual difference of deleted-root
psi variations, and has a proved zero in every periodic gap. The uniform
quotient decay of that difference closes the interpolation argument.
Thus every discriminant Hamiltonian direction fixes the actual
angle/angle bracket. Its zero value remains to be established.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}

/-- The entire actual angle/angle spectral variation vanishes at
every parameter, including coincident roots and periodic terminals. -/
theorem thetaThetaDiscriminant_eq_zero
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0)
    (w : ℂ) :
    sourceAngularThetaThetaDiscriminantBracket hp hp1 h2p n m s φ.val w = 0 := by
  obtain ⟨ρ,hρlp,hρ⟩ := D.exists_thetaThetaDiscriminant_gapZero_sequence h2p n m φ hn hm
  let h : DeletedCoeff p m := (fderiv ℂ (s m) φ.val)
    (sourceHamiltonianDirection h2p (sourceAngularThetaDifferential hp hp1 n s φ.val))
  let v : DeletedCoeff p n := (fderiv ℂ (s n) φ.val)
    (sourceHamiltonianDirection h2p (sourceAngularThetaDifferential hp hp1 m s φ.val))
  have hzero (k : ℤ) :
      sourcePsiCandidateVariation m (s m φ.val : Coeff p) (h : Coeff p) (ρ k)-
        sourcePsiCandidateVariation n (s n φ.val : Coeff p) (v : Coeff p) (ρ k) = 0 := by
    have he := D.thetaThetaDiscriminant_eq_root_variations h2p n m φ hn hm (ρ k)
    rw [(hρ k).2,mul_zero] at he
    exact he.symm
  have hall := sourcePsiCandidateVariation_sub_eq_zero_of_gapZero_sequence hp hp1 φ ρ hρlp
    (fun k => (hρ k).1) m n (s m φ.val : Coeff p) (h : Coeff p)
      (s n φ.val : Coeff p) (v : Coeff p) h.property v.property hzero
  have he := D.thetaThetaDiscriminant_eq_root_variations h2p n m φ hn hm w
  have hw := congrFun hall w
  change sourcePsiCandidateVariation m (s m φ.val : Coeff p) (h : Coeff p) w-
    sourcePsiCandidateVariation n (s n φ.val : Coeff p) (v : Coeff p) w = 0 at hw
  rw [hw] at he
  exact (mul_eq_zero.mp he).resolve_left (by norm_num)

/-- The actual scalar angle/angle bracket commutes with every
discriminant functional in either bracket orientation. -/
theorem sourceBracket_discriminant_thetaTheta_eq_zero
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0)
    (w : ℂ) :
    sourceBracket h2p (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w)
      (sourceAngularThetaThetaBracket hp hp1 h2p n m s) φ.val = 0 := by
  rw [sourceBracket_antisymm]
  change -sourceAngularThetaThetaDiscriminantBracket hp hp1 h2p n m s φ.val w = 0
  rw [D.thetaThetaDiscriminant_eq_zero h2p n m φ hn hm w,neg_zero]

/-- The actual Hamiltonian direction of the angle/angle bracket
is isospectral; its discriminant derivatives all vanish. -/
theorem sourceHamiltonianVector_thetaTheta_isospectral
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    SourceIsospectralDirection hp φ.val
      (sourceHamiltonianVector h2p (sourceAngularThetaThetaBracket hp hp1 h2p n m s) φ.val) := by
  intro w
  change (fderiv ℂ (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ.val)
    (sourceHamiltonianVector h2p (sourceAngularThetaThetaBracket hp hp1 h2p n m s) φ.val) = 0
  rw [fderiv_apply_sourceHamiltonianVector]
  exact D.sourceBracket_discriminant_thetaTheta_eq_zero h2p n m φ hn hm w

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
