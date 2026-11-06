import NLS.MKdV.MiuraGardnerTransfer
import NLS.ZakharovShabat.SourceAngularThetaActionCanonical
import NLS.ZakharovShabat.SourceAngularThetaDifferential

/-! # The actual restricted NLS angle has Gardner bracket delta with J_n

The normalized psi family and local NLS angles are supplied by the checked
common-domain construction. Their phase is pulled back along the literal
L2 diagonal; its logarithmic differential is the derivative of every local
angle representative. Only the angle's own gap is required to be open.
-/
noncomputable section
open Set Complex NLS.Poisson NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

structure MiuraNLSAngleFamily where
  base : Set (CoeffPair 2)
  beta : Set (CoeffPair 2)
  domain : Set (CoeffPair 2)
  psi : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n
  data : SourceAngularThetaCommonDomainData (by simp) (by norm_num) base beta domain psi

theorem nonempty_miuraNLSAngleFamily : Nonempty MiuraNLSAngleFamily := by
  obtain ⟨W₀,B,W,_,_,_,_,_,_,s,D⟩ :=
    exists_sourceAngularTheta_theorem13_1_iv (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num)
  exact ⟨⟨W₀,B,W,s,D⟩⟩

def miuraNLSAngleFamily : MiuraNLSAngleFamily := Classical.choice nonempty_miuraNLSAngleFamily

def miuraThetaPhase (m : ℕ) (a : Coeff 2) : ℂ :=
  sourceAngularThetaAnalyticPhase (by simp) (by norm_num) m miuraNLSAngleFamily.psi (scalarL2Diagonal a)

def miuraThetaDifferential (m : ℕ) (a : Coeff 2) : Coeff 2 →L[ℂ] ℂ :=
  (2*I*miuraThetaPhase m a)⁻¹ • fderiv ℂ (miuraThetaPhase m) a

/-- The pullback differential is the logarithmic derivative of the actual
restricted phase, rather than a cotangent prescribed by a bracket identity. -/
theorem miuraThetaDifferential_eq_source (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m : ℕ)
    (hm : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion (a,a))) (periodOnePotential_mem _) m ≠ 0) :
    miuraThetaDifferential m (scalarInclusion a) =
      (sourceAngularThetaDifferential (by simp) (by norm_num) m miuraNLSAngleFamily.psi
        (sobolevSourceInclusion (a,a))).comp scalarL2Diagonal := by
  let ψ := realDiagonalH1Source a ha
  have hp := miuraNLSAngleFamily.data.theta_phase_analytic m ψ.val
    ⟨miuraNLSAngleFamily.data.real_subset ψ.property,hm⟩
  have hc : DifferentiableAt ℂ (sourceAngularThetaAnalyticPhase (by simp) (by norm_num) m miuraNLSAngleFamily.psi)
      (scalarL2Diagonal (scalarInclusion a)) := by
    rw [scalarL2Diagonal_scalarInclusion]
    exact hp.differentiableAt
  unfold miuraThetaDifferential
  have hd : fderiv ℂ (miuraThetaPhase m) (scalarInclusion a) =
      (fderiv ℂ (sourceAngularThetaAnalyticPhase (by simp) (by norm_num) m miuraNLSAngleFamily.psi)
        (scalarL2Diagonal (scalarInclusion a))).comp scalarL2Diagonal := by
    exact (hc.hasFDerivAt.comp (scalarInclusion a) scalarL2Diagonal.hasFDerivAt).fderiv
  rw [hd]
  apply ContinuousLinearMap.ext
  intro v
  simp only [miuraThetaPhase,sourceAngularThetaDifferential,ContinuousLinearMap.comp_apply,smul_apply,
    scalarL2Diagonal_scalarInclusion]

def miuraThetaGardnerBracket (m n : ℕ) (a : Coeff 2) : ℂ :=
  miuraThetaDifferential m a (l2GardnerDirection (miuraL2Action n) a)

theorem miuraThetaGardnerBracket_eq_kronecker (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hangle : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sobolevSourceInclusion (a,a))) (periodOnePotential_mem _) m ≠ 0) :
    miuraThetaGardnerBracket m n (scalarInclusion a) = if m = n then 1 else 0 := by
  rw [miuraThetaGardnerBracket,miuraThetaDifferential_eq_source a ha m hangle,
    miuraGardner_cotangent_transfer a ha n hn]
  let ψ : realTypeSourceLocus 2 := ⟨(realDiagonalH1Source a ha).val,(realDiagonalH1Source a ha).property⟩
  change sourceAngularThetaFunctionalBracket (by simp) (by norm_num) le_rfl m miuraNLSAngleFamily.psi
      (sourceComplexAction (by simp) (by norm_num) n) ψ.val -
    sourceAngularThetaFunctionalBracket (by simp) (by norm_num) le_rfl m miuraNLSAngleFamily.psi
      (sourceComplexAction (by simp) (by norm_num) (-(n : ℤ))) ψ.val = _
  rw [miuraNLSAngleFamily.data.thetaAction_eq_kronecker le_rfl m n ψ hangle,
    miuraNLSAngleFamily.data.thetaAction_eq_kronecker le_rfl m (-(n : ℤ)) ψ hangle]
  have hneg : (m : ℤ) ≠ -(n : ℤ) := by omega
  simp only [hneg,ite_false,sub_zero]
  by_cases he : m = n
  · subst n
    simp
  · have hcast : (m : ℤ) ≠ (n : ℤ) := by exact_mod_cast he
    simp only [he,hcast,ite_false]

/-- The printed angle domain can equivalently be expressed using the
independent physical mKdV action. The action index n may have a closed gap. -/
theorem miuraThetaGardnerBracket_of_action_ne_zero (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hangle : miuraMKdVAction a ha m ≠ 0) :
    miuraThetaGardnerBracket m n (scalarInclusion a) = if m = n then 1 else 0 := by
  apply miuraThetaGardnerBracket_eq_kronecker a ha m n hm hn
  intro hg
  change miuraNLSRight a m-miuraNLSLeft a m = 0 at hg
  have hi := (miuraNLSAction_zero_iff_endpoints a ha m).mpr (sub_eq_zero.mp hg).symm
  exact hangle ((miuraMKdVAction_nonnegative_and_zero_iff a ha m hm).2.2.mpr hi)

end NLS.MKdV
