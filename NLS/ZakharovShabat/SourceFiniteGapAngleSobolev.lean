import NLS.ZakharovShabat.SourceFiniteGapAngleWeighted
import NLS.ZakharovShabat.SourceFiniteGapSobolevTime

/-!
# The actual finite-gap angle Hamiltonian in H¹

The weighted tangent gives a unique H¹ lift, preserving the original
Fourier coefficients. The actual action-reduction curve differentiates
to this vector in H¹ at every time before its selected action collapses.
-/
noncomputable section
open Set Filter Topology NLS.Poisson
namespace NLS.ZakharovShabat

theorem sobolevSourceInclusion_injective : Function.Injective sobolevSourceInclusion := by
  intro a b hab
  apply Prod.ext
  · apply Subtype.ext
    funext n
    simpa only [sobolevSourceInclusion_fst] using congrArg (fun φ : CoeffPair 2 => φ.fst n) hab
  · apply Subtype.ext
    funext n
    simpa only [sobolevSourceInclusion_snd] using congrArg (fun φ : CoeffPair 2 => φ.snd n) hab

namespace SourceBirkhoffMapComplexData
variable {W₀ B W V₀ C V : Set (CoeffPair 2)}
  {s u : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- No Sobolev regularity of the angle vector is supplied as a hypothesis. -/
theorem existsUnique_finiteGap_thetaHamiltonian_sobolev
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0) :
    ∃! v : ScalarDomain 2 × ScalarDomain 2, sobolevSourceInclusion v =
      sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n u φ.val := by
  let a := sourceFiniteGapSobolevPair (by simp) (by norm_num) φ hf
  let w := SpectralWeight.sobolev 1 (by norm_num)
  let ξ := sobolevNormalizedCoordinates a
  have hdecode : normalizedWeightedSource w ξ = φ.val :=
    (normalizedWeightedSource_sobolevNormalizedCoordinates a).trans
      (sobolevSourceInclusion_sourceFiniteGapSobolevPair φ hf)
  have hreal : IsRealType (CoeffPair.toMax 2 ξ) :=
    (sobolevNormalizedCoordinates_realType_iff a).mpr (by
      rw [sobolevSourceInclusion_sourceFiniteGapSobolevPair]; exact φ.property)
  have hφ : (⟨normalizedWeightedSource w ξ,normalizedWeightedSource_realType w ξ hreal⟩ :
      realTypeSourceSubmodule 2) = φ := Subtype.ext hdecode
  obtain ⟨v,hv,_⟩ := D.existsUnique_finiteGap_thetaHamiltonian_weighted E w ξ hreal
    (by simpa only [hφ] using hf) n (by simpa only [hdecode] using hn)
  have he : sobolevSourceInclusion (sobolevNormalizedCoordinates.symm v) =
      sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n u φ.val := by
    rw [← normalizedWeightedSource_sobolevNormalizedCoordinates,
      ContinuousLinearEquiv.apply_symm_apply,hv,hdecode]
  exact ⟨sobolevNormalizedCoordinates.symm v,he,
    fun v' hv' => sobolevSourceInclusion_injective (hv'.trans he.symm)⟩

/-- The coefficient-preserving H¹ angle tangent at an actual finite-gap source. -/
def finiteGapThetaSobolevVector
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0) :
    ScalarDomain 2 × ScalarDomain 2 :=
  (D.existsUnique_finiteGap_thetaHamiltonian_sobolev E φ hf n hn).exists.choose

theorem finiteGapThetaSobolevVector_inclusion
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0) :
    sobolevSourceInclusion (D.finiteGapThetaSobolevVector E φ hf n hn) =
      sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n u φ.val :=
  (D.existsUnique_finiteGap_thetaHamiltonian_sobolev E φ hf n hn).exists.choose_spec

/-- The lifted vector decreases exactly its selected action, with the
same sign and Kronecker normalization in the actual H¹ direction. -/
theorem finiteGapThetaSobolevVector_action
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0) (k : ℤ) :
    (fderiv ℂ (sourceComplexAction (by simp) (by norm_num) k) φ.val)
      (sobolevSourceInclusion (D.finiteGapThetaSobolevVector E φ hf n hn)) =
      -(if n = k then 1 else 0) := by
  rw [D.finiteGapThetaSobolevVector_inclusion E φ hf n hn,
    sourceAngularThetaHamiltonianVector,apply_sourceHamiltonianDirection,sourceBivector_antisymm]
  exact congrArg Neg.neg (E.thetaAction_eq_kronecker le_rfl n k φ hn)

/-- On an open selected gap the constructed H¹ angle vector is nonzero. -/
theorem finiteGapThetaSobolevVector_ne_zero
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0) :
    D.finiteGapThetaSobolevVector E φ hf n hn ≠ 0 := by
  intro hz
  have he := D.finiteGapThetaSobolevVector_action E φ hf n hn n
  simp only [hz,map_zero,ite_true] at he
  norm_num at he

/-- The original angle flow is differentiable in the physical H¹ topology
throughout its full pre-collapse interval, with the actual lifted tangent. -/
theorem hasDerivAt_hilbertActionReduction_sobolev
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0)
    (t : ℝ) (ht : t < (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re) :
    HasDerivAt (fun r => sourceFiniteGapSobolevPair (by simp) (by norm_num)
      (D.hilbertActionReduction φ n r) (D.hilbertActionReduction_mem_finiteGap φ hf n r))
      (D.finiteGapThetaSobolevVector E (D.hilbertActionReduction φ n t)
        (D.hilbertActionReduction_mem_finiteGap φ hf n t) n
        (D.hilbertActionReduction_gap_ne_zero n φ (hilbert_action_pos_of_gap_ne_zero φ n hn) ht)) t := by
  let γ := D.hilbertActionReduction φ n
  let hγf := D.hilbertActionReduction_mem_finiteGap φ hf n
  let ξ := fun r => sourceFiniteGapSobolevPair (by simp) (by norm_num) (γ r) (hγf r)
  have hγ := D.hasDerivAt_hilbertActionReduction_thetaHamiltonian E n φ
    (hilbert_action_pos_of_gap_ne_zero φ n hn) ht
  obtain ⟨K,hK⟩ := exists_sourceFiniteGap_closedGapTail (by simp) (by norm_num) φ hf
  have htail (r : ℝ) (k : ℤ) (hk : K ≤ k.natAbs) :
      canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (γ r).val)
        (periodOnePotential_mem _) k = 0 := by
    have hkn : k ≠ n := by intro he; subst k; exact hn (hK n hk)
    exact D.hilbertActionReduction_gap_zero_of_ne φ n k hkn r (hK k hk)
  have hξ : DifferentiableAt ℝ ξ t := differentiableAt_sourceFiniteGapSobolevPair
    γ hγf t hγ.differentiableAt K (Filter.Eventually.of_forall htail)
  have hd := (sobolevSourceInclusion.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hξ.hasDerivAt
  change HasDerivAt (fun r => sobolevSourceInclusion (ξ r)) (sobolevSourceInclusion (deriv ξ t)) t at hd
  have hinc : sobolevSourceInclusion (deriv ξ t) =
      sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n u (γ t).val := by
    apply HasDerivAt.unique (f := fun r => (γ r).val) _ hγ
    simpa only [ξ,Function.comp_def,sobolevSourceInclusion_sourceFiniteGapSobolevPair] using hd
  have he := sobolevSourceInclusion_injective (hinc.trans
    (D.finiteGapThetaSobolevVector_inclusion E (γ t) (hγf t) n
      (D.hilbertActionReduction_gap_ne_zero n φ (hilbert_action_pos_of_gap_ne_zero φ n hn) ht)).symm)
  exact he ▸ hξ.hasDerivAt

/-- The lift is independent of both the auxiliary Birkhoff realization
and the normalized angle family. -/
theorem finiteGapThetaSobolevVector_independent
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    {W₀' B' W' V₀' C' V' : Set (CoeffPair 2)}
    {s' u' : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    (D' : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀' B' W' s')
    (E' : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀' C' V' u')
    (φ : realTypeSourceSubmodule 2) (hf : φ ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem _) n ≠ 0) :
    D.finiteGapThetaSobolevVector E φ hf n hn = D'.finiteGapThetaSobolevVector E' φ hf n hn := by
  apply sobolevSourceInclusion_injective
  rw [D.finiteGapThetaSobolevVector_inclusion E φ hf n hn,
    D'.finiteGapThetaSobolevVector_inclusion E' φ hf n hn]
  exact (D.hilbertActionReductionVector_eq_thetaHamiltonian E n φ hn).symm.trans
    (D.hilbertActionReductionVector_eq_thetaHamiltonian E' n φ hn)

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
