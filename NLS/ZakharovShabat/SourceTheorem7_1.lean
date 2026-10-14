import NLS.ZakharovShabat.SourceActionCommonNeighborhood
import NLS.ZakharovShabat.SourceThetaSpectralPhase
import NLS.ZakharovShabat.SourceAngularRegularFourier

/-!
# Theorem 7.1: actual source actions and angles on a common neighborhood

Every finite exponent above one has one neighborhood for all actions and
all open-gap angle charts. The real angles are classes modulo 2π, while
their complex analytic phases and representatives retain the modulo-π
convention. The canonical brackets use the actual regular cotangents.
-/

noncomputable section
open Set Complex NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The three source assertions, with one neighborhood and one actual angular family. -/
structure SourceTheorem7_1Data (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W₀ B V W : Set (CoeffPair p)) (s : (k : ℤ) → CoeffPair p → DeletedCoeff p k) : Prop where
  angular : SourceAngularThetaCommonDomainData hp hp1 W₀ B V s
  source_open : IsOpen W
  real_subset : realTypeSourceLocus p ⊆ W
  source_subset : W ⊆ V
  actions_analytic : ∀ n : ℤ, AnalyticOnNhd ℂ (sourceComplexAction hp hp1 n) W ∧
    AnalyticOnNhd ℝ (sourceComplexAction hp hp1 n) W
  actions_real : ∀ n : ℤ, ∀ φ : realTypeSourceLocus p,
    0 ≤ (sourceComplexAction hp hp1 n φ.val).re ∧ (sourceComplexAction hp hp1 n φ.val).im = 0 ∧
    (sourceComplexAction hp hp1 n φ.val = 0 ↔ sourcePeriodicGapDisplacement hp hp1 φ.val n = 0)
  open_gap : ∀ n : ℤ, IsOpen {φ : CoeffPair p | φ ∈ W ∧
    canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0}
  angle_phase_analytic : ∀ n : ℤ, AnalyticOnNhd ℂ (sourceAngularThetaAnalyticPhase hp hp1 n s)
    {φ : CoeffPair p | φ ∈ W ∧ canonicalPeriodicGap hp hp1
      (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0}
  real_angle_phase : ∀ n : ℤ, ∀ φ : realTypeSourceLocus p,
    canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0 →
    ‖sourceAngularThetaRealPhase hp hp1 n s φ.val‖ = 1 ∧
    (sourceAngularThetaRealPhase hp hp1 n s φ.val)^2 = sourceAngularThetaAnalyticPhase hp hp1 n s φ.val ∧
    Complex.exp (Complex.I*((sourceAngularThetaRealAngle hp hp1 n s φ.val).toReal : ℂ)) =
      sourceAngularThetaRealPhase hp hp1 n s φ.val
  local_angles : ∀ n : ℤ, ∀ φ ∈ W,
    canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0 →
    ∃ U : Set (CoeffPair p), ∃ θ : CoeffPair p → ℂ,
      IsOpen U ∧ φ ∈ U ∧ U ⊆ W ∧ AnalyticOnNhd ℂ θ U ∧ AnalyticOnNhd ℝ θ U ∧
      (∀ ψ ∈ U,
        canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0 ∧
        Complex.exp (2*Complex.I*θ ψ) = sourceAngularThetaAnalyticPhase hp hp1 n s ψ ∧
        fderiv ℂ θ ψ = sourceAngularThetaDifferential hp hp1 n s ψ ∧
        (IsRealType (CoeffPair.toMax p ψ) → (θ ψ).im = 0)) ∧
      (IsRealType (CoeffPair.toMax p φ) → sourceAngularThetaRealAngle hp hp1 n s φ = ((θ φ).re : Real.Angle))
  canonical : ∀ n m : ℤ, ∀ φ : realTypeSourceLocus p,
    (sourceActionRegularCotangent hp hp1 n φ).bivector (sourceActionRegularCotangent hp hp1 m φ) = 0 ∧
    (∀ hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0,
      ∀ hm : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) m ≠ 0,
      (angular.thetaRegularCotangent n φ hn).bivector (angular.thetaRegularCotangent m φ hm) = 0) ∧
    (∀ hn : canonicalPeriodicGap hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n ≠ 0,
      (angular.thetaRegularCotangent n φ hn).bivector (sourceActionRegularCotangent hp hp1 m φ) =
        if n = m then 1 else 0)

/-- Theorem 7.1, with every field constructed for the full finite exponent range. -/
theorem sourceTheorem7_1 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W₀ B V W : Set (CoeffPair p), ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
      SourceTheorem7_1Data hp hp1 W₀ B V W s := by
  obtain ⟨W₀,B,V,_,_,_,_,_,_,s,D⟩ := exists_sourceAngularTheta_theorem13_1_iv hp hp1
  obtain ⟨A,hAo,hAr,hA⟩ := exists_sourceAction_common_analytic_neighborhood hp hp1
  let W := A ∩ V
  have hWo : IsOpen W := hAo.inter D.source_open
  have hWr : realTypeSourceLocus p ⊆ W := fun φ hφ => ⟨hAr hφ,D.real_subset hφ⟩
  refine ⟨W₀,B,V,W,s,{
    angular := D
    source_open := hWo
    real_subset := hWr
    source_subset := inter_subset_right
    actions_analytic := fun n => ⟨(hA n).1.mono inter_subset_left,(hA n).2.mono inter_subset_left⟩
    actions_real := fun n φ => sourceComplexAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 n φ.val φ.property
    open_gap := ?_
    angle_phase_analytic := fun n φ hφ => D.theta_phase_analytic n φ ⟨hφ.1.2,hφ.2⟩
    real_angle_phase := fun n φ hg => ⟨(D.realThetaPhase_norm_and_sq n φ hg).1,
      (D.realThetaPhase_norm_and_sq n φ hg).2,D.exp_realThetaAngle n φ hg⟩
    local_angles := ?_
    canonical := D.corollary13_2_regular }⟩
  · intro n
    have he : {φ : CoeffPair p | φ ∈ W ∧ canonicalPeriodicGap hp hp1
        (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0} =
        A ∩ {φ : CoeffPair p | φ ∈ V ∧ canonicalPeriodicGap hp hp1
          (periodOnePotential φ) (periodOnePotential_mem φ) n ≠ 0} := by
      ext φ
      simp only [W,mem_ofPred_eq,mem_inter_iff,and_assoc]
    rw [he]
    exact hAo.inter (D.open_gap n)
  · intro n φ hφ hg
    obtain ⟨O,U,c,T,r,R,z₀,ρ,δ,ε,hφU,hUV,hδ,E⟩ := D.local_charts n φ hφ.2 hg
    let θ := sourceAngularThetaCauchyRepresentative hp hp1 n s (c n) r R z₀ ρ ε
    have hβ := (D.beta_series.analytic_correction n).mono (hUV.trans D.source_subset)
    have hθ : AnalyticOnNhd ℂ θ U := E.theta_representative_analytic hβ
    have hr (ψ : CoeffPair p) (hψ : ψ ∈ U) (hreal : IsRealType (CoeffPair.toMax p ψ)) :
        (θ ψ).im = 0 := E.theta_representative_im_eq_zero_of_realType
      D.psi.toSourcePsiIsolatingComplexExtension ψ hψ hreal (D.correction_real ψ (hUV hψ) hreal n)
    exact ⟨U ∩ W,θ,E.angle.source_open.inter hWo,⟨hφU,hφ⟩,inter_subset_right,
      hθ.mono inter_subset_left,(hθ.mono inter_subset_left).restrictScalars,
      fun ψ hψ => ⟨E.gap_ne_zero ψ hψ.1,(E.theta_phase_eq_exp_representative ψ hψ.1).symm,
        (E.thetaDifferential_eq_fderiv_representative hβ ψ hψ.1).symm,hr ψ hψ.1⟩,
      fun hreal => E.realThetaAngle_eq_representative φ hφU hδ hg (hr φ hφU hreal)⟩

end NLS.ZakharovShabat
