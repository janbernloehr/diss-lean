import NLS.ZakharovShabat.SourceNativeMomentumActionFactors
import NLS.ZakharovShabat.SourceSobolevFourthActionCurves
import NLS.ZakharovShabat.SourceSection20MomentumBracket

/-! # Physical momentum action derivatives with the exact 2πn normalization

The original actual action-reduction Hamiltonian is calibrated by Section20.
The same native curve and raw unit action direction identify every open
partial derivative of the actual momentum factor. Closed action cotangents
vanish and do not require choosing an artificial boundary frequency.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The original unit-speed reduction differentiates any genuine local
action factor in the negative raw unit direction. -/
theorem deriv_nativeMomentum_actionReduction_of_factor
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (z : FourthSobolevBirkhoffTarget) (n : ℤ)
    (V : Set FourthSobolevBirkhoffTarget) (hV : IsOpen V) (hz : z ∈ V)
    (H : FourthSobolevActions → ℂ) (hH : AnalyticAt ℂ H (fourthSobolevActions z))
    (hrec : ∀ y ∈ V, H (fourthSobolevActions y) = D.nativeMomentumBirkhoff y)
    (ha : 0 < RealCoeff.pairAction (originalWeightedRealTarget fourthSobolevSpectralWeight z) n) :
    deriv (fun t : ℝ => D.nativeMomentumBirkhoff
      (WeightedRealCoeff.actionReduction (sourceFrequencyWeight fourthSobolevSpectralWeight)
        (fun k => fourthSobolevSpectralWeight.one_le (2*k)) z n t)) 0 =
      -fderiv ℂ H (fourthSobolevActions z) (fourthSobolevActionDirection n) := by
  let γ := WeightedRealCoeff.actionReduction (sourceFrequencyWeight fourthSobolevSpectralWeight)
    (fun k => fourthSobolevSpectralWeight.one_le (2*k)) z n
  have hγ : ContinuousAt γ 0 := (WeightedRealCoeff.hasDerivAt_actionReduction_zero _ _ z n).continuousAt
  have hz₀ : γ 0 = z := WeightedRealCoeff.actionReduction_zero _ _ z n
  have hev : ∀ᶠ t in 𝓝 (0:ℝ), γ t ∈ V := by
    apply hγ.tendsto.eventually
    rw [hz₀]
    exact hV.mem_nhds hz
  have het : ∀ᶠ t in 𝓝 (0:ℝ), t ≤ RealCoeff.pairAction
      (originalWeightedRealTarget fourthSobolevSpectralWeight z) n :=
    eventually_le_nhds ha
  have heq : (fun t : ℝ => D.nativeMomentumBirkhoff (γ t)) =ᶠ[𝓝 0]
      (fun t => H (fourthSobolevActions z-(t:ℂ) • fourthSobolevActionDirection n)) := by
    filter_upwards [hev,het] with t ht hta
    rw [← hrec _ ht,fourthSobolevActions_actionReduction z n ha t hta]
  have hline : HasDerivAt (fun t : ℝ => fourthSobolevActions z-t • fourthSobolevActionDirection n)
      (-fourthSobolevActionDirection n) 0 := by
    simpa only [one_smul,id_eq] using! ((hasDerivAt_id (0:ℝ)).smul_const (fourthSobolevActionDirection n)).const_sub (fourthSobolevActions z)
  have hbase : fourthSobolevActions z-(0:ℝ) • fourthSobolevActionDirection n = fourthSobolevActions z := by simp
  have hh : HasFDerivAt H ((fderiv ℂ H (fourthSobolevActions z)).restrictScalars ℝ)
      (fourthSobolevActions z-(0:ℝ) • fourthSobolevActionDirection n) :=
    hbase.symm ▸ hH.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have hd := hh.comp_hasDerivAt 0 hline
  have he := hd.deriv
  change deriv (fun t : ℝ => H (fourthSobolevActions z-t • fourthSobolevActionDirection n)) 0 = _ at he
  exact heq.deriv_eq.trans (by simpa only [map_neg] using! he)

/-- The independently defined second physical Hamiltonian has the exact
negative unit-action derivative at every real finite-gap open action. -/
theorem deriv_physicalActionReductionHamiltonian_two
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential φ.val)
      (periodOnePotential_mem _) n ≠ 0) :
    deriv (D.physicalActionReductionHamiltonian φ hf n 2) 0 = -(2*(Real.pi:ℂ)*n) := by
  obtain ⟨V₀,V,X,u,E,Wa,A,C,U,Q⟩ := sourceSection20_original (p := 2) (by simp) (by norm_num)
  have he := D.finiteGap_momentum_bracket_normalized E.previous.original_theta_common_domain
    Q.toSourceFullAbelianDifferentialData A φ hf n hn
  rw [D.finiteGap_momentum_bracket_eq_physical_deriv E.previous.original_theta_common_domain φ hf n hn] at he
  exact neg_eq_iff_eq_neg.mp he

private theorem physicalMomentum_congr (φ ψ : realTypeSourceSubmodule 2)
    (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (hg : ψ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (he : φ = ψ) :
    sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) φ hf 2 =
      sourceFiniteGapNLSHamiltonian (by simp) (by norm_num) ψ hg 2 := by
  subst ψ
  rfl

/-- The actual native momentum reduction curve is the original physical
second Hamiltonian along the same finite-gap source curve, at every time. -/
theorem nativeMomentum_actionReduction_eq_physical
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource)
    (hf : originalWeightedRealSource fourthSobolevSpectralWeight a ∈ sourceFiniteGapLocus (by simp) (by norm_num)) (n : ℤ) :
    (fun t : ℝ => D.nativeMomentumBirkhoff (WeightedRealCoeff.actionReduction
      (sourceFrequencyWeight fourthSobolevSpectralWeight)
      (fun k => fourthSobolevSpectralWeight.one_le (2*k))
      (D.originalWeightedRealMap fourthSobolevSpectralWeight a) n t)) =
      D.physicalActionReductionHamiltonian (originalWeightedRealSource fourthSobolevSpectralWeight a) hf n 2 := by
  funext t
  have hfg := D.sobolevActionReduction_mem_finiteGap (3/2) (by norm_num) a hf n t
  change sourceFourthSobolevMomentum (D.sobolevActionReduction (3/2) (by norm_num) a n t) = _
  rw [sourceFourthSobolevMomentum_eq_finiteGap _ hfg]
  have he := D.originalWeightedRealSource_sobolevActionReduction (3/2) (by norm_num) a n t
  exact physicalMomentum_congr _ _ hfg
    (D.hilbertActionReduction_mem_finiteGap _ hf n t) he

/-- Every actual local physical momentum factor has partial derivative
2πn at an open finite-gap action, in the unchanged raw action direction. -/
theorem nativeMomentum_action_factor_derivative
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (a : NativeFourthSobolevSource)
    (hf : originalWeightedRealSource fourthSobolevSpectralWeight a ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (V : Set FourthSobolevBirkhoffTarget) (hV : IsOpen V)
    (haV : D.originalWeightedRealMap fourthSobolevSpectralWeight a ∈ V)
    (H : FourthSobolevActions → ℂ)
    (hH : AnalyticAt ℂ H (fourthSobolevActions (D.originalWeightedRealMap fourthSobolevSpectralWeight a)))
    (hrec : ∀ y ∈ V, H (fourthSobolevActions y) = D.nativeMomentumBirkhoff y)
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (originalWeightedRealSource fourthSobolevSpectralWeight a).val)
      (periodOnePotential_mem _) n ≠ 0) :
    fderiv ℂ H (fourthSobolevActions (D.originalWeightedRealMap fourthSobolevSpectralWeight a))
      (fourthSobolevActionDirection n) = 2*(Real.pi:ℂ)*n := by
  have hpos : 0 < RealCoeff.pairAction (originalWeightedRealTarget fourthSobolevSpectralWeight
      (D.originalWeightedRealMap fourthSobolevSpectralWeight a)) n := by
    rw [D.originalWeightedRealTarget_map]
    change 0 < RealCoeff.pairAction (D.hilbertRealHomeomorph _) n
    rw [D.hilbert_pairAction_eq]
    exact hilbert_action_pos_of_gap_ne_zero _ n hn
  have he := D.deriv_nativeMomentum_actionReduction_of_factor
    (D.originalWeightedRealMap fourthSobolevSpectralWeight a) n V hV haV H hH hrec hpos
  rw [D.nativeMomentum_actionReduction_eq_physical a hf n,
    D.deriv_physicalActionReductionHamiltonian_two _ hf n hn] at he
  exact neg_injective he.symm

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData

