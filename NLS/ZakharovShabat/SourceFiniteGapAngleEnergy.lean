import NLS.ZakharovShabat.SourceFiniteGapAngleSobolev
import NLS.ZakharovShabat.SourceFiniteGapOpenFrequency
import NLS.ZakharovShabat.SourcePhysicalEnergyActionDifferential

/-!
# The physical H¹ energy bracket at real finite-gap sources

The H¹ energy is differentiated along the actual lifted angle flow. Its
negative directional derivative is the physical frequency. Whenever the
energy differential is represented by a Hilbert cotangent, the same value
is exactly the original source Poisson bivector, with its original sign.
-/
noncomputable section
open Set Filter Topology NLS.Poisson
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W V₀ C V : Set (CoeffPair 2)}
  {s u : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- The physical action derivative is the full H¹ energy differential
applied to the constructed H¹ angle tangent at every pre-collapse time. -/
theorem hasDerivAt_physicalActionReductionHamiltonian_sobolev
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0)
    (t : ℝ) (ht : t < (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re) :
    HasDerivAt (D.physicalActionReductionHamiltonian φ hf n 3)
      (fderiv ℂ periodOneSobolevHamiltonian
        (sourceFiniteGapSobolevPair (by simp) (by norm_num) (D.hilbertActionReduction φ n t)
          (D.hilbertActionReduction_mem_finiteGap φ hf n t))
        (D.finiteGapThetaSobolevVector E (D.hilbertActionReduction φ n t)
          (D.hilbertActionReduction_mem_finiteGap φ hf n t) n
          (D.hilbertActionReduction_gap_ne_zero n φ (hilbert_action_pos_of_gap_ne_zero φ n hn) ht))) t := by
  have hξ := D.hasDerivAt_hilbertActionReduction_sobolev E φ hf n hn t ht
  have hd := ((analyticAt_periodOneSobolevHamiltonian _).differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt t hξ
  apply hd.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun r =>
    (periodOneSobolevHamiltonian_sourceFiniteGapSobolevPair (by simp) (by norm_num)
      (D.hilbertActionReduction φ n r) (D.hilbertActionReduction_mem_finiteGap φ hf n r)).symm)

/-- The independently defined physical frequency equals the actual energy
bracket; no contour moment or assumed Sobolev tangent enters the definition. -/
theorem finiteGapOpenFrequency_eq_sobolev_energy_bracket
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0) :
    D.finiteGapOpenFrequency φ hf n hn =
      -(fderiv ℂ periodOneSobolevHamiltonian (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf)
        (D.finiteGapThetaSobolevVector E φ hf n hn)) := by
  have hd := D.hasDerivAt_physicalActionReductionHamiltonian_sobolev E φ hf n hn 0
    (hilbert_action_pos_of_gap_ne_zero φ n hn)
  simpa only [finiteGapOpenFrequency,D.hilbertActionReduction_zero] using congrArg Neg.neg hd.deriv

/-- Any Hilbert cotangent representing the full H¹ energy differential
gives the same original Poisson bracket. -/
theorem finiteGap_energy_bivector_eq
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0)
    (L : CoeffPair 2 →L[ℂ] ℂ)
    (hL : fderiv ℂ periodOneSobolevHamiltonian
      (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf) = L.comp sobolevSourceInclusion) :
    sourceBivector le_rfl (sourceAngularThetaDifferential (by simp) (by norm_num) n u φ.val) L =
      D.finiteGapOpenFrequency φ hf n hn := by
  rw [D.finiteGapOpenFrequency_eq_sobolev_energy_bracket E φ hf n hn,hL,
    ContinuousLinearMap.comp_apply,D.finiteGapThetaSobolevVector_inclusion E φ hf n hn,
    sourceAngularThetaHamiltonianVector,apply_sourceHamiltonianDirection,sourceBivector_antisymm]

/-- A physical Hilbert cotangent exists at each actual finite-gap source,
and its angle bracket is the physical frequency. -/
theorem exists_finiteGap_energy_cotangent_bracket
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num)) :
    ∃ L : CoeffPair 2 →L[ℂ] ℂ,
      HasFDerivAt periodOneSobolevHamiltonian (L.comp sobolevSourceInclusion)
        (sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf) ∧
      ∀ (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0),
        sourceBivector le_rfl (sourceAngularThetaDifferential (by simp) (by norm_num) n u φ.val) L =
          D.finiteGapOpenFrequency φ hf n hn := by
  obtain ⟨Y,P,_,_,_,_,v,hs,hlocal⟩ := exists_sourceAbelianMoment_localCharts (p := 2) (by simp) (by norm_num)
  choose C hC using hlocal
  let A : SourceAbelianMomentAtlas (by simp) (by norm_num) Y v := ⟨C⟩
  let a := sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf
  have hi : sobolevSourceInclusion a = φ.val := sobolevSourceInclusion_sourceFiniteGapSobolevPair φ hf
  let b : realTypeSobolevSourceLocus := ⟨a,by rw [hi]; exact φ.property⟩
  have hφ : (⟨sobolevSourceInclusion b.val,b.property⟩ : realTypeSourceSubmodule 2) = φ := Subtype.ext hi
  obtain ⟨S,hS⟩ := A.exists_periodOneSobolevHamiltonian_finiteGap_differential
    hs.toSourcePsiIsolatingComplexExtension b (by
      change (⟨sobolevSourceInclusion b.val,b.property⟩ : realTypeSourceSubmodule 2) ∈ sourceFiniteGapLocus (by simp) (by norm_num)
      simpa only [hφ] using hf)
  let L : CoeffPair 2 →L[ℂ] ℂ := ∑ n ∈ S,
    (A.ordinaryPhaseFrequency le_rfl ⟨sobolevSourceInclusion b.val,b.property⟩ n : ℂ) •
      fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) (sobolevSourceInclusion b.val)
  change fderiv ℂ periodOneSobolevHamiltonian a = L.comp sobolevSourceInclusion at hS
  refine ⟨L,?_,?_⟩
  · exact hS ▸ (analyticAt_periodOneSobolevHamiltonian a).differentiableAt.hasFDerivAt
  · intro n hn
    exact D.finiteGap_energy_bivector_eq E φ hf n hn _ hS

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
