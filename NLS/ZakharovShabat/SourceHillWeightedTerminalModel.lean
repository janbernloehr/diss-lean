import NLS.ZakharovShabat.SourceNormalizedMidpointSymbol
import NLS.ZakharovShabat.SourceSignedTerminalSequence
import NLS.SequenceSpaces.CompactUnitSymbolDerivative
import NLS.SequenceSpaces.HalfFourierEquiv

/-! The literal Hill spectral terminal in its native signed minus-half
Sobolev target. The normalized midpoint factor is differentiated in the
bounded symbol norm; its entire derivative correction is compact. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The exact constant remaining after applying the native target weight. -/
def sourceHillTerminalScale : ℂ := (Real.sqrt Real.pi : ℂ)/(Real.sqrt 2 : ℂ)

/-- The fixed native weighted Fourier principal operator for Dirac inputs. -/
def sourceHillTerminalFourier : CoeffPair 2 →L[ℂ] WeightedCoeff (Weight.signedSobolev (-1/2)) 2 :=
  sourceHillTerminalScale •
    ((WeightedCoeff.weightIsometry (Weight.signedSobolev (-1/2)) 2).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      sourceSignedTerminalFourier)

/-- The fixed principal operator retains the exact weighted Fourier coefficients. -/
theorem sourceHillTerminalFourier_weighted_apply (h : CoeffPair 2) (k : ℤ) :
    (WeightedCoeff.weightIsometry (Weight.signedSobolev (-1/2)) 2
      (sourceHillTerminalFourier h)) k = sourceHillTerminalScale*sourceSignedTerminalFourier h k := by
  change (WeightedCoeff.weightIsometry (Weight.signedSobolev (-1/2)) 2)
    (sourceHillTerminalScale • (WeightedCoeff.weightIsometry (Weight.signedSobolev (-1/2)) 2).symm
      (sourceSignedTerminalFourier h)) k = _
  rw [map_smul,LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- The actual weighted spectral terminal with its normalized midpoint symbol. -/
def sourceHillTerminalModel (ψ : CoeffPair 2) : WeightedCoeff (Weight.signedSobolev (-1/2)) 2 :=
  WeightedCoeff.boundedSymbolBilinear (Weight.signedSobolev (-1/2))
    (sourceNormalizedMidpointSymbol (by simp) (by norm_num) ψ)
    (sourceHillTerminalScale • (WeightedCoeff.weightIsometry (Weight.signedSobolev (-1/2)) 2).symm
      (sourceSignedTerminalSequence ψ))

/-- Weighting retains the exact bounded coefficient factors. -/
theorem sourceHillTerminalModel_weighted_apply (ψ : CoeffPair 2) (k : ℤ) :
    (WeightedCoeff.weightIsometry (Weight.signedSobolev (-1/2)) 2
      (sourceHillTerminalModel ψ)) k = sourceHillTerminalScale*
        sourceNormalizedMidpointSymbol (by simp) (by norm_num) ψ k*sourceSignedTerminalSequence ψ k := by
  let w := Weight.signedSobolev (-1/2)
  let a := (WeightedCoeff.weightIsometry w 2).symm (sourceSignedTerminalSequence ψ)
  have he : (w k : ℂ)*a.val k = sourceSignedTerminalSequence ψ k :=
    congrArg (fun b : Coeff 2 => b k) ((WeightedCoeff.weightIsometry w 2).apply_symm_apply _)
  change (w k : ℂ)*(sourceNormalizedMidpointSymbol (by simp) (by norm_num) ψ k*
    (sourceHillTerminalScale*a.val k)) = _
  calc
    _ = sourceHillTerminalScale*sourceNormalizedMidpointSymbol (by simp) (by norm_num) ψ k*
        ((w k : ℂ)*a.val k) := by ring
    _ = _ := by rw [he]

@[simp] theorem sourceHillTerminalModel_zero_mode (ψ : CoeffPair 2) :
    (sourceHillTerminalModel ψ).val 0 = 0 := by
  have he := sourceHillTerminalModel_weighted_apply ψ 0
  change (Weight.signedSobolev (-1/2) 0 : ℂ)*(sourceHillTerminalModel ψ).val 0 = _ at he
  simpa only [Weight.signedSobolev_zero,ofReal_one,one_mul,
    sourceSignedTerminalSequence_zero,mul_zero] using he

/-- One common complex domain supplies the exact native weighted terminal
and compact derivative remainder, including the differentiated midpoint factor. -/
theorem exists_sourceHillTerminalModel_compact_derivative_domain :
    ∃ W : Set (CoeffPair 2), IsOpen W ∧ realTypeSourceLocus 2 ⊆ W ∧
      AnalyticOnNhd ℂ sourceHillTerminalModel W ∧ ∀ ψ ∈ W,
        (∀ n : ℕ+,
          (WeightedCoeff.weightIsometry (Weight.signedSobolev (-1/2)) 2 (sourceHillTerminalModel ψ)) ((n:ℕ):ℤ) =
            sourceHillTerminalScale*sourcePositiveNormalizedMidpoint (by simp) (by norm_num) n ψ*
              sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) ((n:ℕ):ℤ) 1 ψ ∧
          (WeightedCoeff.weightIsometry (Weight.signedSobolev (-1/2)) 2 (sourceHillTerminalModel ψ)) (-((n:ℕ):ℤ)) =
            sourceHillTerminalScale*sourcePositiveNormalizedMidpoint (by simp) (by norm_num) n ψ*
              sourceGapWeightedEtaTerminalCoordinate (by simp) (by norm_num) ((n:ℕ):ℤ) (-1) ψ) ∧
        IsCompactOperator (fderiv ℂ sourceHillTerminalModel ψ-sourceHillTerminalFourier) := by
  obtain ⟨W₀,_,_,_,V,hV,_,hrealV,s,H⟩ := sourceLemma12_12 (p := 2) (by simp) (by norm_num)
  obtain ⟨U,hU,hrealU,hT,hdata⟩ := exists_sourceSignedTerminalSequence_compact_derivative_domain
  let w := Weight.signedSobolev (-1/2)
  let L := (WeightedCoeff.weightIsometry w 2).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let g := fun ψ : CoeffPair 2 => sourceHillTerminalScale • L (sourceSignedTerminalSequence ψ)
  have hg : AnalyticOnNhd ℂ g U := fun ψ hψ =>
    (((L.analyticAt _).comp (hT ψ hψ)).const_smul (c := sourceHillTerminalScale))
  have ha : AnalyticOnNhd ℂ sourceHillTerminalModel (V ∩ U) := by
    intro ψ hψ
    exact ((WeightedCoeff.boundedSymbolBilinear w).analyticAt_bilinear _).comp
      ((H.normalized_midpoint_symbol_data.2 ψ hψ.1).prod (hg ψ hψ.2))
  refine ⟨V ∩ U,hV.inter hU,fun ψ hψ => ⟨hrealV hψ,hrealU hψ⟩,ha,fun ψ hψ => ⟨?_,?_⟩⟩
  · intro n
    have hn : (0 : ℤ) < ((n:ℕ):ℤ) := by exact_mod_cast n.pos
    constructor
    · rw [sourceHillTerminalModel_weighted_apply,H.normalized_midpoint_symbol_data.1 ψ hψ.1,
        Coeff.evenUnitExtension_positive,(hdata ψ hψ.2).1 ((n:ℕ):ℤ) hn]
    · rw [sourceHillTerminalModel_weighted_apply,H.normalized_midpoint_symbol_data.1 ψ hψ.1,
        Coeff.evenUnitExtension_negative,(hdata ψ hψ.2).2.1 (-((n:ℕ):ℤ)) (by omega),neg_neg]
  · have hunit := WeightedCoeff.isCompactOperator_fderiv_boundedSymbol_sub w (by simp)
      (sourceNormalizedMidpointSymbol (p := 2) (by simp) (by norm_num)) g ψ
      (H.normalized_midpoint_symbol_data.2 ψ hψ.1) (hg ψ hψ.2)
      (H.normalized_midpoint_symbol_unit_tail ψ hψ.1)
    have hd : fderiv ℂ g ψ = (sourceHillTerminalScale • L).comp (fderiv ℂ sourceSignedTerminalSequence ψ) :=
      (((sourceHillTerminalScale • L).hasFDerivAt).comp ψ
        (hT ψ hψ.2).differentiableAt.hasFDerivAt).fderiv
    have hfree : IsCompactOperator (fderiv ℂ g ψ-sourceHillTerminalFourier) := by
      have he : fderiv ℂ g ψ-sourceHillTerminalFourier =
          (sourceHillTerminalScale • L).comp
            (fderiv ℂ sourceSignedTerminalSequence ψ-sourceSignedTerminalFourier) := by
        rw [hd]
        ext h
        simp only [sourceHillTerminalFourier,ContinuousLinearMap.comp_apply,sub_apply,smul_apply,L,w,map_sub]
      rw [he]
      exact ((hdata ψ hψ.2).2.2).clm_comp (sourceHillTerminalScale • L)
    have he : fderiv ℂ sourceHillTerminalModel ψ-sourceHillTerminalFourier =
        (fderiv ℂ sourceHillTerminalModel ψ-fderiv ℂ g ψ)+
          (fderiv ℂ g ψ-sourceHillTerminalFourier) := by abel
    rw [he]
    exact hunit.add hfree

end NLS.ZakharovShabat
