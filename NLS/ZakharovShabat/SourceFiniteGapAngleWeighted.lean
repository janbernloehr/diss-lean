import NLS.ZakharovShabat.SourceFiniteGapTranslationLift
import NLS.ZakharovShabat.SourceHilbertActionReductionFiniteGap
import NLS.ZakharovShabat.SourceHilbertAngleFlowUnique

/-!
# Weighted regularity of the actual finite-gap angle Hamiltonian

The original action-reduction curve keeps a fixed closed-gap tail. Its
analytic weighted reconstruction therefore lifts the actual theta tangent.
Injectivity of the decoding map makes the weighted tangent unique.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W V₀ C V : Set (CoeffPair 2)}
  {s u : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- At a weighted real finite-gap source, the original angle Hamiltonian
has a unique tangent with the same spectral weight. -/
theorem existsUnique_finiteGap_thetaHamiltonian_weighted
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (E : SourceAngularThetaCommonDomainData (by simp) (by norm_num) V₀ C V u)
    (w : SpectralWeight) (a : CoeffPair 2)
    (ha : IsRealType (CoeffPair.toMax 2 a))
    (hf : (⟨normalizedWeightedSource w a,normalizedWeightedSource_realType w a ha⟩ :
      realTypeSourceSubmodule 2) ∈ sourceFiniteGapLocus (by simp) (by norm_num))
    (n : ℤ) (hn : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (normalizedWeightedSource w a)) (periodOnePotential_mem _) n ≠ 0) :
    ∃! v : CoeffPair 2, normalizedWeightedSource w v =
      sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n u
        (normalizedWeightedSource w a) := by
  let φ : realTypeSourceSubmodule 2 :=
    ⟨normalizedWeightedSource w a,normalizedWeightedSource_realType w a ha⟩
  let γ : ℝ → CoeffPair 2 := fun t => (D.hilbertActionReduction φ n t).val
  have hpos := hilbert_action_pos_of_gap_ne_zero φ n hn
  have hγ : HasDerivAt γ
      (sourceAngularThetaHamiltonianVector (by simp) (by norm_num) le_rfl n u φ.val) 0 := by
    simpa only [γ,D.hilbertActionReduction_zero] using
      D.hasDerivAt_hilbertActionReduction_thetaHamiltonian E n φ hpos hpos
  obtain ⟨K,hK⟩ := exists_sourceFiniteGap_closedGapTail (by simp) (by norm_num) φ hf
  have htail (t : ℝ) (k : ℤ) (hk : K ≤ k.natAbs) :
      canonicalPeriodicGap (by simp) (by norm_num) (periodOnePotential (γ t))
        (periodOnePotential_mem _) k = 0 := by
    have hkn : k ≠ n := by intro he; subst k; exact hn (hK n hk)
    exact D.hilbertActionReduction_gap_zero_of_ne φ n k hkn t (hK k hk)
  obtain ⟨ξ,hξ,_,hdecode⟩ := exists_differentiableAt_sourceFiniteGap_weightedLift
    (by simp) (by norm_num) w a ha hf K γ 0 hγ.differentiableAt
    (by simp only [γ,D.hilbertActionReduction_zero,φ])
    (Filter.Eventually.of_forall (fun t => (D.hilbertActionReduction φ n t).property))
    (Filter.Eventually.of_forall htail)
  have hd := ((normalizedWeightedSourceCLM (p := 2) w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hξ.hasDerivAt
  have hd' : HasDerivAt γ (normalizedWeightedSource w (deriv ξ 0)) 0 :=
    hd.congr_of_eventuallyEq (by filter_upwards [hdecode] with t ht; exact ht.symm)
  refine ⟨deriv ξ 0,hd'.unique hγ,?_⟩
  intro v hv
  exact normalizedWeightedSource_injective w (hv.trans (hd'.unique hγ).symm)

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
