import NLS.ZakharovShabat.SourceAngularEtaDiscriminantKernel
import NLS.ZakharovShabat.SourceAngularBetaDiscriminantValue

/-! # The actual theta/discriminant identity

The single eta cotangent supplies exactly the diagonal omitted by the
full beta correction. Their actual filled kernels cancel that omission,
giving the normalized psi numerator with the original factor and sign
at every spectral parameter. The same identity determines the flow of
the single-valued angle phase.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}

/-- The actual theta/discriminant bracket equals minus half the
normalized psi numerator at every spectral parameter. Only the
selected angle gap must be open; its terminal may be periodic. -/
theorem thetaDiscriminant_eq
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n : ℤ) (φ : realTypeSourceLocus p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (w : ℂ) :
    sourceAngularThetaFunctionalBracket hp hp1 h2p n s
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ.val =
      -sourcePsiCandidate n (w,(s n φ.val : Coeff p))/2 := by
  obtain ⟨V,U,c,T,r,R,z₀,ρ,δ,ε,hφU,hUW,_,C⟩ :=
    D.local_charts n φ.val (D.real_subset φ.property) hgap
  rw [sourceAngularThetaFunctionalBracket,C.thetaDifferential_eq_eta_add_betaCorrection
    ((D.beta_series.analytic_correction n).mono (hUW.trans D.source_subset)) φ.val hφU]
  simp only [map_add,add_apply]
  change sourceBivector h2p (sourceAngularEtaDifferential hp hp1 n s φ.val)
      (fderiv ℂ (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ.val)+
    sourceBracket h2p (sourceAngularBetaCorrection hp hp1 n s)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ.val = _
  rw [D.sourceBivector_etaDifferential_discriminant_eq_kernel h2p n φ hgap w,
    D.sourceBracket_betaCorrection_discriminant_eq h2p n φ w]
  ring

/-- With the discriminant cotangent first, the actual bracket has
the original positive psi/2 normalization. -/
theorem sourceBivector_discriminant_theta_eq
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n : ℤ) (φ : realTypeSourceLocus p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (w : ℂ) :
    sourceBivector h2p (sourceDiscriminantCotangent hp w φ.val)
      (sourceAngularThetaDifferential hp hp1 n s φ.val) =
      sourcePsiCandidate n (w,(s n φ.val : Coeff p))/2 := by
  rw [sourceBivector_antisymm]
  change -(sourceAngularThetaFunctionalBracket hp hp1 h2p n s
    (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ.val) = _
  rw [D.thetaDiscriminant_eq h2p n φ hgap w]
  ring

/-- The actual single-valued phase has the discriminant Hamiltonian
velocity `-i phase psi`, independent of an angle representative. -/
theorem sourceBracket_thetaPhase_discriminant_eq
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n : ℤ) (φ : realTypeSourceLocus p)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (w : ℂ) :
    sourceBracket h2p (sourceAngularThetaAnalyticPhase hp hp1 n s)
      (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ.val =
      -I*sourceAngularThetaAnalyticPhase hp hp1 n s φ.val*
        sourcePsiCandidate n (w,(s n φ.val : Coeff p)) := by
  have hn := D.theta_phase_ne_zero φ.val (D.real_subset φ.property) n hgap
  have he := (sourceAngularThetaFunctionalBracket_eq_iff hp hp1 h2p n s
    (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ.val
    (-sourcePsiCandidate n (w,(s n φ.val : Coeff p))/2) hn).mp
      (D.thetaDiscriminant_eq h2p n φ hgap w)
  rw [he]
  ring

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
