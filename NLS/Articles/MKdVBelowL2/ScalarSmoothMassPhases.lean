import NLS.Articles.MKdVBelowL2.ScalarSmoothFourierApproximation
import NLS.Articles.MKdVBelowL2.PhysicalNonzeroBirkhoffIndex
import NLS.ZakharovShabat.SourceHilbertMassDivergence
import NLS.Dynamics.FixedTimeMassPhaseTuning

/-! # Controlled smooth real approximants with prescribed physical mass phase

The approximation takes place in the original real Fourier source norm.
Native H⁴ representatives retain the actual scalar distribution coefficients,
and their original physical mass diverges at every non-Hilbert datum.
-/
noncomputable section
set_option autoImplicit false
open Set Filter Topology Complex NLS.Fourier
open scoped ENNReal ContDiff
namespace NLS.Articles.MKdVBelowL2
open NLS.ZakharovShabat NLS.Dynamics
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual Hilbert mass remains a nonnegative original physical quantity. -/
theorem fourthClassicalMass_eq_norm_fst (a : FourthClassicalSource) :
    fourthClassicalMass a = ((‖(originalWeightedRealSource _ a).val.fst‖^2 : ℝ) : ℂ) := by
  unfold fourthClassicalMass
  rw [sourceHilbertMass_eq_half_norm_sq_of_realType _ (originalWeightedRealSource _ a).property]
  congr 1
  change ‖originalWeightedRealSource _ a‖^2/2 = _
  rw [realTypeSource_norm_sq_eq_two_mul_fst]
  ring

theorem fourthClassicalMass_smul (r : ℝ) (a : FourthClassicalSource) :
    fourthClassicalMass (r • a) = (r^2 : ℝ)*fourthClassicalMass a := by
  rw [fourthClassicalMass_eq_norm_fst,fourthClassicalMass_eq_norm_fst]
  have he : originalWeightedRealSource _ (r • a) = r • originalWeightedRealSource _ a :=
    (originalWeightedRealSourceCLM _).map_smul r a
  rw [he]
  change ((‖r • (originalWeightedRealSource _ a).val.fst‖^2 : ℝ) : ℂ) = _
  rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  push_cast
  ring

/-- Smooth scalar cutoffs have actual diagonal native representatives
whose included raw sources converge in the original finite-p source norm. -/
theorem exists_fourthClassicalSource_sequence (hp : p ≠ ⊤) (h2p : 2 ≤ p)
    (u : PhysicalScalarRealInput p) :
    ∃ a : ℕ → FourthClassicalSource,
      (∀ j, (originalWeightedRealSource _ (a j)).val.fst = (originalWeightedRealSource _ (a j)).val.snd) ∧
      (∀ j, ContDiff ℝ ∞ (fun x : ℝ => (nativeSobolevPhysicalJetCLM 4 0 (by omega) (a j)).1 (x : AddCircle (2:ℝ)))) ∧
      Tendsto (fun j => realTypeSourceExponentInclusion h2p (originalWeightedRealSource _ (a j)))
        atTop (𝓝 (physicalRealCoefficientsCL (physicalScalarPairCLM u))) := by
  have hex (j : ℕ) : ∃ a : FourthClassicalSource,
      (originalWeightedRealSource _ a).val.fst = (originalWeightedRealSource _ a).val.snd ∧
      ContDiff ℝ ∞ (fun x : ℝ => (nativeSobolevPhysicalJetCLM 4 0 (by omega) a).1 (x : AddCircle (2:ℝ))) ∧
      realTypeSourceExponentInclusion h2p (originalWeightedRealSource _ a) =
        physicalRealCoefficientsCL (physicalScalarPairCLM (physicalScalarTruncate j u)) := by
    obtain ⟨f,a,hf,_,_,ha,h0,h1,h2⟩ := exists_fourthClassicalSource_of_smooth_scalar h2p
      (physicalScalarTruncate j u) (isSmoothPhysicalScalarInput_truncate j u)
    have hj : (fun x : ℝ => (nativeSobolevPhysicalJetCLM 4 0 (by omega) a).1 (x : AddCircle (2:ℝ))) = f := by
      simpa only [fourthClassicalPhysicalValue,fourthClassicalPhysicalFlow,fourthClassicalSourceFlow_zero] using h0
    refine ⟨a,ha,?_,?_⟩
    · rw [hj]
      exact hf
    · have he := physicalRealCoefficients_exponent_of_same_distributions h2p
        (fourthClassicalPhysicalInput a) (physicalScalarPairCLM (physicalScalarTruncate j u)) ⟨h1,h2⟩
      simpa only [fourthClassicalPhysicalInput,ContinuousLinearEquiv.apply_symm_apply] using he
  choose a ha hs he using hex
  refine ⟨a,ha,hs,?_⟩
  simp_rw [he]
  exact (physicalRealCoefficientsCL.continuous.comp physicalScalarPairCLM.continuous).continuousAt.tendsto.comp
    (tendsto_physicalScalarTruncate hp u)

/-- Absence of a physical Hilbert representative is exactly the source
condition needed by mass divergence. -/
theorem not_mem_sourceHilbertLocus_of_no_physical_hilbert (h2p : 2 ≤ p)
    (u : PhysicalRealInput p) (hu : ¬ physicalPairHasHilbertRepresentative u) :
    physicalRealCoefficientsCL u ∉ sourceHilbertLocus h2p := by
  rintro ⟨φ,hφ⟩
  apply hu
  let v : PhysicalRealInput 2 := physicalRealCoefficientsCL.symm φ
  have he : realTypeSourceExponentInclusion h2p (physicalRealCoefficientsCL v) =
      physicalRealCoefficientsCL u := by
    apply Subtype.ext
    change CoeffPair.exponentInclusion h2p (physicalRealCoefficientsCL (physicalRealCoefficientsCL.symm φ)).val = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact congrArg Subtype.val hφ
  obtain ⟨h1,h2⟩ := same_distributions_of_physicalRealCoefficients_exponent h2p v u he
  exact ⟨v,h1.symm,h2.symm⟩

/-- Every such actual native approximation has diverging physical mass. -/
theorem tendsto_fourthClassicalMass_atTop (h2p : 2 ≤ p)
    (u : PhysicalRealInput p) (hu : ¬ physicalPairHasHilbertRepresentative u)
    (a : ℕ → FourthClassicalSource)
    (ha : Tendsto (fun j => realTypeSourceExponentInclusion h2p (originalWeightedRealSource _ (a j)))
      atTop (𝓝 (physicalRealCoefficientsCL u))) :
    Tendsto (fun j => (fourthClassicalMass (a j)).re) atTop atTop :=
  tendsto_sourceHilbertMass_real_atTop h2p _
    (not_mem_sourceHilbertLocus_of_no_physical_hilbert h2p u hu)
    (fun j => originalWeightedRealSource _ (a j)) ha

/-- Arbitrary fixed mass phases are attained along genuinely smooth real
native approximants without changing their original finite-p limit. -/
theorem exists_fourthClassicalSource_sequence_mass_phase
    (hp : p ≠ ⊤) (h2p : 2 ≤ p) (u : PhysicalScalarRealInput p)
    (hu : ¬ physicalPairHasHilbertRepresentative (physicalScalarPairCLM u))
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 ≤ δ) :
    ∃ b : ℕ → FourthClassicalSource,
      (∀ j, (originalWeightedRealSource _ (b j)).val.fst = (originalWeightedRealSource _ (b j)).val.snd) ∧
      (∀ j, ContDiff ℝ ∞ (fun x : ℝ => (nativeSobolevPhysicalJetCLM 4 0 (by omega) (b j)).1 (x : AddCircle (2:ℝ)))) ∧
      Tendsto (fun j => realTypeSourceExponentInclusion h2p (originalWeightedRealSource _ (b j)))
        atTop (𝓝 (physicalRealCoefficientsCL (physicalScalarPairCLM u))) ∧
      ∀ j, Complex.exp (((2*Real.pi*c*(fourthClassicalMass (b j)).re : ℝ) : ℂ)*Complex.I) =
        Complex.exp (((2*Real.pi*δ : ℝ) : ℂ)*Complex.I) := by
  obtain ⟨a,ha,hs,ht⟩ := exists_fourthClassicalSource_sequence hp h2p u
  have hdiv := tendsto_fourthClassicalMass_atTop h2p (physicalScalarPairCLM u) hu a ht
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hdiv.eventually (eventually_gt_atTop 0))
  let a' := fun j : ℕ => a (j+N)
  let M := fun j : ℕ => (fourthClassicalMass (a' j)).re
  have hM (j : ℕ) : 0 < M j := hN (j+N) (Nat.le_add_left N j)
  have hMdiv : Tendsto M atTop atTop := hdiv.comp (tendsto_add_atTop_nat N)
  obtain ⟨α,hα,_,hphase⟩ := exists_mass_phase_scales M hM hMdiv c δ hc hδ
  refine ⟨fun j => α j • a' j,?_,?_,?_,?_⟩
  · intro j
    have he : originalWeightedRealSource _ (α j • a' j) = α j • originalWeightedRealSource _ (a' j) :=
      (originalWeightedRealSourceCLM _).map_smul (α j) (a' j)
    rw [he]
    change (α j • (originalWeightedRealSource _ (a' j)).val).fst =
      (α j • (originalWeightedRealSource _ (a' j)).val).snd
    rw [WithLp.smul_fst,WithLp.smul_snd,ha (j+N)]
  · intro j
    simpa only [map_smul,Prod.smul_fst,ContinuousMap.smul_apply] using (hs (j+N)).const_smul (α j)
  · apply tendsto_subtype_rng.mpr
    have hbase := tendsto_subtype_rng.mp (ht.comp (tendsto_add_atTop_nat N))
    have hlim := hα.smul hbase
    simp only [one_smul] at hlim
    convert hlim using 1
    funext j
    change CoeffPair.exponentInclusion h2p (originalWeightedRealSource _ (α j • a' j)).val = _
    have he : originalWeightedRealSource _ (α j • a' j) = α j • originalWeightedRealSource _ (a' j) :=
      (originalWeightedRealSourceCLM _).map_smul (α j) (a' j)
    rw [he]
    exact (CoeffPair.exponentInclusion h2p).map_smul_of_tower (α j) _
  · intro j
    have hm : (fourthClassicalMass (α j • a' j)).re = (α j)^2*M j := by
      rw [fourthClassicalMass_smul,Complex.mul_re]
      simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,M]
    rw [hm]
    simpa only [mul_assoc] using hphase j

end NLS.Articles.MKdVBelowL2
