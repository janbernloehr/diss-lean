import NLS.Poisson.SourceBracketJacobi
import NLS.ZakharovShabat.SourceAngularThetaLocalExactness
import NLS.ZakharovShabat.SourceAngularThetaActionLocalCanonical

/-! # Actual action stationarity of the theta/theta bracket

The constructed local angle primitives obey the proved canonical
theta/action relations as complex germs. Jacobi therefore makes the
actual theta/theta bracket stationary along every actual action
Hamiltonian direction. Its canonical zero value remains a separate
spectral calculation.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}

/-- Every actual action Hamiltonian direction fixes the actual
theta/theta bracket at every real source with both selected gaps open. -/
theorem fderiv_thetaTheta_action_eq_zero
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m k : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    (fderiv ℂ (sourceAngularThetaThetaBracket hp hp1 h2p n m s) φ.val)
      (sourceHamiltonianVector h2p (sourceComplexAction hp hp1 k) φ.val) = 0 := by
  have hφ : φ.val ∈ W := D.real_subset φ.property
  obtain ⟨F,hF,hFn⟩ := D.exists_local_thetaDifferential_fderiv n φ.val hφ hn
  obtain ⟨G,hG,hGm⟩ := D.exists_local_thetaDifferential_fderiv m φ.val hφ hm
  let A := sourceComplexAction hp hp1 k
  have hA : AnalyticAt ℂ A φ.val :=
    analyticAt_sourceComplexAction_of_realType hp hp1 k φ.val φ.property
  have hFG : sourceAngularThetaThetaBracket hp hp1 h2p n m s =ᶠ[𝓝 φ.val]
      sourceBracket h2p F G := by
    filter_upwards [hFn,hGm] with ψ hψn hψm
    change sourceBivector h2p (sourceAngularThetaDifferential hp hp1 n s ψ)
      (sourceAngularThetaDifferential hp hp1 m s ψ) =
        sourceBivector h2p (fderiv ℂ F ψ) (fderiv ℂ G ψ)
    rw [hψn,hψm]
  have hFA : sourceBracket h2p F A =ᶠ[𝓝 φ.val] (fun _ => if n = k then 1 else 0) := by
    have he : sourceBracket h2p F A =ᶠ[𝓝 φ.val]
        sourceAngularThetaFunctionalBracket hp hp1 h2p n s A := by
      filter_upwards [hFn] with ψ hψ
      change sourceBivector h2p (fderiv ℂ F ψ) (fderiv ℂ A ψ) =
        sourceBivector h2p (sourceAngularThetaDifferential hp hp1 n s ψ) (fderiv ℂ A ψ)
      rw [hψ]
    exact he.trans (D.eventually_thetaAction_eq_kronecker h2p n k φ hn)
  have hGA : sourceBracket h2p G A =ᶠ[𝓝 φ.val] (fun _ => if m = k then 1 else 0) := by
    have he : sourceBracket h2p G A =ᶠ[𝓝 φ.val]
        sourceAngularThetaFunctionalBracket hp hp1 h2p m s A := by
      filter_upwards [hGm] with ψ hψ
      change sourceBivector h2p (fderiv ℂ G ψ) (fderiv ℂ A ψ) =
        sourceBivector h2p (sourceAngularThetaDifferential hp hp1 m s ψ) (fderiv ℂ A ψ)
      rw [hψ]
    exact he.trans (D.eventually_thetaAction_eq_kronecker h2p m k φ hm)
  have hAF : sourceBracket h2p A F =ᶠ[𝓝 φ.val] (fun _ => -(if n = k then 1 else 0)) := by
    filter_upwards [hFA] with ψ hψ
    rw [sourceBracket_antisymm,hψ]
  have hdGA : fderiv ℂ (sourceBracket h2p G A) φ.val = 0 :=
    hGA.fderiv_eq.trans (hasFDerivAt_const (if m = k then (1 : ℂ) else 0) φ.val).fderiv
  have hdAF : fderiv ℂ (sourceBracket h2p A F) φ.val = 0 :=
    hAF.fderiv_eq.trans (hasFDerivAt_const (-(if n = k then (1 : ℂ) else 0)) φ.val).fderiv
  have h₂ : sourceBracket h2p (sourceBracket h2p G A) F φ.val = 0 := by
    change sourceBivector h2p (fderiv ℂ (sourceBracket h2p G A) φ.val) (fderiv ℂ F φ.val) = 0
    rw [hdGA]; simp only [map_zero,zero_apply]
  have h₃ : sourceBracket h2p (sourceBracket h2p A F) G φ.val = 0 := by
    change sourceBivector h2p (fderiv ℂ (sourceBracket h2p A F) φ.val) (fderiv ℂ G φ.val) = 0
    rw [hdAF]; simp only [map_zero,zero_apply]
  have hj := sourceBracket_jacobi h2p F G A φ.val hF hG hA
  rw [h₂,h₃,add_zero,add_zero] at hj
  rw [hFG.fderiv_eq,fderiv_apply_sourceHamiltonianVector]
  exact hj

/-- The actual theta/theta bracket, regarded as a scalar functional,
commutes with every actual action, including collapsed action gaps. -/
theorem sourceBracket_thetaTheta_action_eq_zero
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m k : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0) :
    sourceBracket h2p (sourceAngularThetaThetaBracket hp hp1 h2p n m s)
      (sourceComplexAction hp hp1 k) φ.val = 0 := by
  rw [← fderiv_apply_sourceHamiltonianVector]
  exact D.fderiv_thetaTheta_action_eq_zero h2p n m k φ hn hm

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
