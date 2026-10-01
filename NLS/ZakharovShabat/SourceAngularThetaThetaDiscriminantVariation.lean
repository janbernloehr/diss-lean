import NLS.ZakharovShabat.SourceAngularThetaThetaActionStationarity
import NLS.ZakharovShabat.SourceAngularThetaDiscriminantLocal
import NLS.ZakharovShabat.SourcePsiSourceVariation
import NLS.ZakharovShabat.SourceFunctionalActionContour

/-! # The spectral discriminant variation of the actual angle/angle bracket

Jacobi and the local theta/discriminant identity express this variation
as an antisymmetric difference of actual normalized psi variations.
It is entire in the spectral parameter, and action stationarity makes
its canonical-root-weighted period zero on every actual action chart.
The vanishing of the entire variation itself is not assumed.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual angle/angle bracket differentiated in the discriminant
Hamiltonian direction at a fixed spectral parameter. -/
def sourceAngularThetaThetaDiscriminantBracket
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (n m : ℤ) (s : (j : ℤ) → CoeffPair p → DeletedCoeff p j)
    (φ : CoeffPair p) (w : ℂ) : ℂ :=
  sourceBracket h2p (sourceAngularThetaThetaBracket hp hp1 h2p n m s)
    (fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w) φ

/-- The literal spectral variation is entire, without a noncoincident
parameter restriction or an assumed spectral-flow identity. -/
theorem analyticOnNhd_sourceAngularThetaThetaDiscriminantBracket
    (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : (2 : ℝ≥0∞) ≤ p)
    (n m : ℤ) (s : (j : ℤ) → CoeffPair p → DeletedCoeff p j) (φ : CoeffPair p) :
    AnalyticOnNhd ℂ (sourceAngularThetaThetaDiscriminantBracket hp hp1 h2p n m s φ) univ := by
  let L := sourceBivector h2p
    (fderiv ℂ (sourceAngularThetaThetaBracket hp hp1 h2p n m s) φ)
  intro w _
  exact (L.analyticAt _).comp
    ((analyticOnNhd_sourceDiscriminantCotangent_joint hp hp1 (w,φ) (mem_univ _)).comp
      (f := fun z : ℂ => (z,φ)) (analyticAt_id.prod analyticAt_const))

namespace SourceAngularThetaCommonDomainData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (j : ℤ) → CoeffPair p → DeletedCoeff p j}

/-- Jacobi identifies the actual spectral variation with the
antisymmetric mixed angle/normalized-numerator brackets. -/
theorem thetaThetaDiscriminant_eq_psi_brackets
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0)
    (w : ℂ) :
    2*sourceAngularThetaThetaDiscriminantBracket hp hp1 h2p n m s φ.val w =
      sourceAngularThetaFunctionalBracket hp hp1 h2p m s
        (fun ψ : CoeffPair p => sourcePsiCandidate n (w,(s n ψ : Coeff p))) φ.val-
      sourceAngularThetaFunctionalBracket hp hp1 h2p n s
        (fun ψ : CoeffPair p => sourcePsiCandidate m (w,(s m ψ : Coeff p))) φ.val := by
  have hφ : φ.val ∈ W := D.real_subset φ.property
  obtain ⟨F,hF,hFn⟩ := D.exists_local_thetaDifferential_fderiv n φ.val hφ hn
  obtain ⟨G,hG,hGm⟩ := D.exists_local_thetaDifferential_fderiv m φ.val hφ hm
  let H := fun ψ : CoeffPair p => canonicalDiscriminant hp (periodOnePotential ψ) w
  have hH : AnalyticAt ℂ H φ.val :=
    (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1 (w,φ.val) (mem_univ _)).comp
      (f := fun ψ : CoeffPair p => (w,ψ)) (analyticAt_const.prod analyticAt_id)
  have hFG : sourceAngularThetaThetaBracket hp hp1 h2p n m s =ᶠ[𝓝 φ.val] sourceBracket h2p F G := by
    filter_upwards [hFn,hGm] with ψ hψn hψm
    change sourceBivector h2p (sourceAngularThetaDifferential hp hp1 n s ψ)
      (sourceAngularThetaDifferential hp hp1 m s ψ) =
        sourceBivector h2p (fderiv ℂ F ψ) (fderiv ℂ G ψ)
    rw [hψn,hψm]
  have hFH : sourceBracket h2p F H =ᶠ[𝓝 φ.val]
      sourceAngularThetaFunctionalBracket hp hp1 h2p n s H := by
    filter_upwards [hFn] with ψ hψ
    change sourceBivector h2p (fderiv ℂ F ψ) (fderiv ℂ H ψ) = _
    rw [← hψ]
    rfl
  have hGH : sourceBracket h2p G H =ᶠ[𝓝 φ.val]
      sourceAngularThetaFunctionalBracket hp hp1 h2p m s H := by
    filter_upwards [hGm] with ψ hψ
    change sourceBivector h2p (fderiv ℂ G ψ) (fderiv ℂ H ψ) = _
    rw [← hψ]
    rfl
  have hdFH : fderiv ℂ (sourceBracket h2p F H) φ.val =
      -(1/2 : ℂ) • fderiv ℂ (fun ψ : CoeffPair p => sourcePsiCandidate n (w,(s n ψ : Coeff p))) φ.val :=
    hFH.fderiv_eq.trans (D.fderiv_thetaDiscriminant_eq_numerator h2p n φ hn w)
  have hdGH : fderiv ℂ (sourceBracket h2p G H) φ.val =
      -(1/2 : ℂ) • fderiv ℂ (fun ψ : CoeffPair p => sourcePsiCandidate m (w,(s m ψ : Coeff p))) φ.val :=
    hGH.fderiv_eq.trans (D.fderiv_thetaDiscriminant_eq_numerator h2p m φ hm w)
  have hHF : sourceBracket h2p H F = fun ψ => -sourceBracket h2p F H ψ := by
    funext ψ
    exact sourceBracket_antisymm h2p H F ψ
  have hdHF : fderiv ℂ (sourceBracket h2p H F) φ.val =
      -fderiv ℂ (sourceBracket h2p F H) φ.val := by
    rw [hHF]
    exact fderiv_neg
  have hj := sourceBracket_jacobi h2p F G H φ.val hF hG hH
  change sourceBivector h2p (fderiv ℂ (sourceBracket h2p F G) φ.val) (fderiv ℂ H φ.val)+
    sourceBivector h2p (fderiv ℂ (sourceBracket h2p G H) φ.val) (fderiv ℂ F φ.val)+
    sourceBivector h2p (fderiv ℂ (sourceBracket h2p H F) φ.val) (fderiv ℂ G φ.val) = 0 at hj
  rw [← hFG.fderiv_eq,hdGH,hdHF,hdFH,← hFn.eq_of_nhds,← hGm.eq_of_nhds] at hj
  simp only [map_smul,smul_apply,smul_eq_mul,map_neg,neg_apply] at hj
  rw [sourceBivector_antisymm h2p _ (sourceAngularThetaDifferential hp hp1 n s φ.val),
    sourceBivector_antisymm h2p _ (sourceAngularThetaDifferential hp hp1 m s φ.val)] at hj
  change 2*sourceBivector h2p
    (fderiv ℂ (sourceAngularThetaThetaBracket hp hp1 h2p n m s) φ.val) (fderiv ℂ H φ.val) = _
  change sourceBivector h2p _ (fderiv ℂ H φ.val)+
    -(1/2 : ℂ)*(-(sourceAngularThetaFunctionalBracket hp hp1 h2p n s
      (fun ψ : CoeffPair p => sourcePsiCandidate m (w,(s m ψ : Coeff p))) φ.val))-
    -(1/2 : ℂ)*(-(sourceAngularThetaFunctionalBracket hp hp1 h2p m s
      (fun ψ : CoeffPair p => sourcePsiCandidate n (w,(s n ψ : Coeff p))) φ.val)) = 0 at hj
  linear_combination 2*hj

/-- The spectral variation is the difference of two actual entire
root variations, with the root directions supplied by the actual
angle Hamiltonian cotangents. -/
theorem thetaThetaDiscriminant_eq_root_variations
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0)
    (w : ℂ) :
    2*sourceAngularThetaThetaDiscriminantBracket hp hp1 h2p n m s φ.val w =
      sourcePsiCandidateVariation m (s m φ.val : Coeff p)
        ((fderiv ℂ (s m) φ.val)
          (sourceHamiltonianDirection h2p (sourceAngularThetaDifferential hp hp1 n s φ.val)) : Coeff p) w-
      sourcePsiCandidateVariation n (s n φ.val : Coeff p)
        ((fderiv ℂ (s n) φ.val)
          (sourceHamiltonianDirection h2p (sourceAngularThetaDifferential hp hp1 m s φ.val)) : Coeff p) w := by
  have hs := D.psi.toSourcePsiIsolatingComplexExtension
  obtain ⟨a,ha,_,_,_,_,hball,_,_,_,_⟩ := hs.isolation φ
  have hφ₀ := hball (mem_ball_self ha)
  have he := D.thetaThetaDiscriminant_eq_psi_brackets h2p n m φ hn hm w
  change 2*sourceAngularThetaThetaDiscriminantBracket hp hp1 h2p n m s φ.val w =
    sourceBivector h2p (sourceAngularThetaDifferential hp hp1 m s φ.val)
      (fderiv ℂ (fun ψ : CoeffPair p => sourcePsiCandidate n (w,(s n ψ : Coeff p))) φ.val)-
    sourceBivector h2p (sourceAngularThetaDifferential hp hp1 n s φ.val)
      (fderiv ℂ (fun ψ : CoeffPair p => sourcePsiCandidate m (w,(s m ψ : Coeff p))) φ.val) at he
  rw [sourceBivector_antisymm h2p (sourceAngularThetaDifferential hp hp1 m s φ.val) _,
    sourceBivector_antisymm h2p (sourceAngularThetaDifferential hp hp1 n s φ.val) _,
    ← apply_sourceHamiltonianDirection,← apply_sourceHamiltonianDirection,
    hs.fderiv_numerator_eq_root_variation n φ.val _ hφ₀ w,
    hs.fderiv_numerator_eq_root_variation m φ.val _ hφ₀ w] at he
  linear_combination he

/-- Action stationarity forces the entire spectral variation to have
zero canonical-root-weighted period on every actual action chart. -/
theorem thetaThetaDiscriminant_period_eq_zero
    (D : SourceAngularThetaCommonDomainData hp hp1 W₀ B W s)
    (h2p : (2 : ℝ≥0∞) ≤ p) (n m k : ℤ) (φ : realTypeSourceLocus p)
    (hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0)
    (hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0)
    (ch : SourceRealActionBallChart hp hp1 k) (hφ : φ.val ∈ ball ch.center ch.radius) :
    (∮ w in C(ch.spectralCenter,ch.spectralRadius),
      sourceAngularThetaThetaDiscriminantBracket hp hp1 h2p n m s φ.val w /
        sourceCanonicalRoot hp hp1 φ.val w) = 0 := by
  have he := sourceBracket_functional_action_eq_discriminant_circle hp hp1 h2p
    (sourceAngularThetaThetaBracket hp hp1 h2p n m s) k ch φ.val φ.property hφ
  rw [D.sourceBracket_thetaTheta_action_eq_zero h2p n m k φ hn hm] at he
  have hc : -(Real.pi : ℂ)⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero (by exact_mod_cast Real.pi_ne_zero))
  exact (mul_eq_zero.mp he.symm).resolve_left hc

end SourceAngularThetaCommonDomainData
end NLS.ZakharovShabat
