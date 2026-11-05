import NLS.KdV.HillNativeAbelianActionDerivative

/-! # Exact weighted vector pushforward of every physical action Hamiltonian -/
noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.KdV

theorem hillNativeAbelian_zero_mode_of_physical
    (η : ℝ) (hη : 0 < η)
    (Z : Coeff 2 → WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : Coeff 2) η))
    (hphysical : ∀ p : RealHillWeightedPotential SpectralWeight.one,
      SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
      Z (SpectralWeight.one.doubleIndex.toCoeff p.val) = hillPhysicalAbelianMap SpectralWeight.one p) :
    ∀ u ∈ ball (0 : Coeff 2) η, (Z u).val 0 = 0 := by
  apply periodOneL2_real_form_identity isOpen_ball (convex_ball (0 : Coeff 2) η).isPreconnected
    (mem_ball_self hη) (fun u => (Z u).val 0) (fun _ => (0 : ℂ))
    (fun u hu => ((WeightedCoeff.evalCLM _ 2 0).analyticAt _).comp (hZa u hu))
    (fun _ _ => analyticAt_const)
  intro u hu hJu
  let p := hillUnitRealSourceLift u hJu
  have he : SpectralWeight.one.doubleIndex.toCoeff p.val = u := hillUnitRealSourceLift_toCoeff _ _
  have hz : Z u = hillPhysicalAbelianMap SpectralWeight.one p := by
    simpa only [he] using hphysical p (by simpa only [he] using hu)
  rw [hz]
  exact (hillPhysicalAbelianMap_real SpectralWeight.one p).1

theorem fderiv_hillNativeAbelian_zero_mode
    (η : ℝ) (Z : Coeff 2 → WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : Coeff 2) η))
    (hzero : ∀ u ∈ ball (0 : Coeff 2) η, (Z u).val 0 = 0)
    (u : Coeff 2) (hu : u ∈ ball (0 : Coeff 2) η) (v : Coeff 2) :
    ((fderiv ℂ Z u) v).val 0 = 0 := by
  let ev := WeightedCoeff.evalCLM (hillAbelianTargetWeight SpectralWeight.one) 2 0
  have hd := ev.hasFDerivAt.comp u (hZa u hu).differentiableAt.hasFDerivAt
  have he : (fun a => ev (Z a)) =ᶠ[𝓝 u] (fun _ : Coeff 2 => (0 : ℂ)) := by
    filter_upwards [isOpen_ball.mem_nhds hu] with a ha
    exact hzero a ha
  have hh := he.fderiv_eq (𝕜 := ℂ)
  change fderiv ℂ (ev ∘ Z) u = fderiv ℂ (fun _ : Coeff 2 => (0 : ℂ)) u at hh
  rw [hd.fderiv] at hh
  have hc : fderiv ℂ (fun _ : Coeff 2 => (0 : ℂ)) u = 0 := (hasFDerivAt_const (0 : ℂ) u).fderiv
  rw [hc] at hh
  exact congrArg (fun L : Coeff 2 →L[ℂ] ℂ => L v) hh

theorem fderiv_hillNativeAbelian_action_vector
    (η : ℝ) (Z : Coeff 2 → WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : Coeff 2) η))
    (hzero : ∀ u ∈ ball (0 : Coeff 2) η, (Z u).val 0 = 0)
    (hphysical : ∀ p : RealHillWeightedPotential SpectralWeight.one,
      SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
      Z (SpectralWeight.one.doubleIndex.toCoeff p.val) = hillPhysicalAbelianMap SpectralWeight.one p)
    (p : RealHillWeightedPotential SpectralWeight.one)
    (hp : SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η)
    (m : ℕ) (hm : 1 ≤ m) :
    (fderiv ℂ Z (SpectralWeight.one.doubleIndex.toCoeff p.val)) (hillUnitActionDirection p m) =
      WeightedCoeff.signedModeGenerator (hillAbelianTargetWeight SpectralWeight.one) m
        (Z (SpectralWeight.one.doubleIndex.toCoeff p.val)) := by
  apply Subtype.ext
  funext j
  cases j with
  | ofNat n =>
    by_cases hn : n = 0
    · subst n
      exact (fderiv_hillNativeAbelian_zero_mode η Z hZa hzero _ hp _).trans
        (WeightedCoeff.signedModeGenerator_zero_mode _ m hm _).symm
    · refine (fderiv_hillNativeAbelian_action_positive η Z hZa hphysical p hp n m (by omega) hm).trans ?_
      refine Eq.trans ?_ (WeightedCoeff.signedModeGenerator_apply _ m _ (n : ℤ)).symm
      have hpneg : (n : ℤ) ≠ -(m : ℤ) := by omega
      have he : (n : ℤ) = (m : ℤ) ↔ m = n := by omega
      simp only [if_neg hpneg,sub_zero,he]
      by_cases hmn : m = n <;> simp [hmn]

  | negSucc n =>
    change ((fderiv ℂ Z (SpectralWeight.one.doubleIndex.toCoeff p.val)) (hillUnitActionDirection p m)).val
      (-((n+1 : ℕ) : ℤ)) = _
    refine (fderiv_hillNativeAbelian_action_negative η Z hZa hphysical p hp (n+1) m (by omega) hm).trans ?_
    refine Eq.trans ?_ (WeightedCoeff.signedModeGenerator_apply _ m _ (-((n+1 : ℕ) : ℤ))).symm
    have hnpos : -((n+1 : ℕ) : ℤ) ≠ (m : ℤ) := by omega
    have he : -((n+1 : ℕ) : ℤ) = -(m : ℤ) ↔ m = n+1 := by omega
    simp only [if_neg hnpos,zero_sub,he]
    by_cases hmn : m = n+1 <;> simp [hmn]

theorem fderiv_hillNativeAbelian_meanZero_action_vector
    (η : ℝ) (Z : Coeff 2 → WeightedCoeff (hillAbelianTargetWeight SpectralWeight.one) 2)
    (hZa : AnalyticOnNhd ℂ Z (ball (0 : Coeff 2) η))
    (hzero : ∀ u ∈ ball (0 : Coeff 2) η, (Z u).val 0 = 0)
    (hphysical : ∀ p : RealHillWeightedPotential SpectralWeight.one,
      SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η →
      Z (SpectralWeight.one.doubleIndex.toCoeff p.val) = hillPhysicalAbelianMap SpectralWeight.one p)
    (p : RealHillWeightedPotential SpectralWeight.one)
    (hmean : (SpectralWeight.one.doubleIndex.toCoeff p.val) 0 = 0)
    (hp : SpectralWeight.one.doubleIndex.toCoeff p.val ∈ ball (0 : Coeff 2) η)
    (m : ℕ) (hm : 1 ≤ m) :
    let a : DeletedCoeff 2 0 := ⟨SpectralWeight.one.doubleIndex.toCoeff p.val,hmean⟩
    let F := WeightedCoeff.meanZeroWeightedMap (hillAbelianTargetWeight SpectralWeight.one) Z
    (fderiv ℂ F a) (hillDeletedActionDirection p m hm) =
      WeightedCoeff.meanZeroSignedModeGenerator (hillAbelianTargetWeight SpectralWeight.one) m (F a) := by
  intro a F
  have hFi : HasFDerivAt F
      ((WeightedCoeff.meanZeroWeightedProjectionCLM (hillAbelianTargetWeight SpectralWeight.one)).comp
        ((fderiv ℂ Z a.val).comp (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).ker.subtypeL)) a := by
    exact (WeightedCoeff.meanZeroWeightedProjectionCLM _).hasFDerivAt.comp a
      (((hZa a.val hp).differentiableAt.hasFDerivAt).comp a
        ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).ker.subtypeL).hasFDerivAt)
  rw [hFi.fderiv]
  change WeightedCoeff.meanZeroWeightedProjectionCLM _
    ((fderiv ℂ Z a.val) (hillUnitActionDirection p m)) = _
  rw [fderiv_hillNativeAbelian_action_vector η Z hZa hzero hphysical p hp m hm]
  exact (WeightedCoeff.meanZeroSignedModeGenerator_projection _ m (Z a.val) (hzero a.val hp)).symm

end NLS.KdV
