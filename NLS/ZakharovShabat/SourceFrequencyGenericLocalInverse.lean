import NLS.ZakharovShabat.SourceFrequencyLocalInverse
import NLS.ZakharovShabat.SourceFrequencyConnectedDomain
import NLS.FunctionalAnalysis.AnalyticFredholmDensity
import NLS.ComplexAnalysis.AnalyticUnitDerivativeInverse

/-! # Corollary 18.2(iv): generic local invertibility of the frequency map

Choose the component containing all real-source actions and the positive
summable action cone. Compactness, analyticity and the computed derivative
at zero give an open dense set with actual two-sided analytic local inverses.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- The actual frequency map is locally analytically invertible on an open
dense subset of a connected action domain containing every real-source
action. The origin and Fredholm conclusions are retained. -/
theorem exists_sourceFrequency_genericLocalInverse (hp : p ≠ ⊤) (hp2 : 2 < p) :
    ∃ hp1 : 1 < p, ∃ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
    ∃ P : Set (CoeffPair p), SourcePsiIsolatingComplexExtension hp hp1 P s ∧
    ∃ W₀ B X : Set (CoeffPair p), ∃ t : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ _D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t,
    ∃ V : Set (Coeff q), IsOpen V ∧ IsPreconnected V ∧ (0 : Coeff q) ∈ V ∧
      (∀ ψ : realTypeSourceSubmodule p, sourceActionSequence (q := q) hp hp1 t ψ.val ∈ V) ∧
      (∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) →
        Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) ∈ V) ∧
      (∃ Y : Set (CoeffPair p), IsOpen Y ∧ realTypeSourceLocus p ⊆ Y ∧ Y ⊆ X ∧
        sourceActionSequence (q := q) hp hp1 t '' Y = V) ∧
      ∃ F : Coeff q → Coeff q, AnalyticOnNhd ℂ F V ∧ AnalyticOnNhd ℝ F V ∧ F 0 = 0 ∧
        (∀ ψ : realTypeSourceSubmodule p, ∀ n,
          F (sourceActionSequence (q := q) hp hp1 t ψ.val) n = A.renormalizedFrequency n ψ.val) ∧
        (∀ b ∈ V,
          IsCompactOperator (fderiv ℂ F b + (2 : ℂ) • ContinuousLinearMap.id ℂ (Coeff q)) ∧
          (fderiv ℂ F b).IsFredholm ∧
          Module.finrank ℂ (fderiv ℂ F b).ker =
            Module.finrank ℂ (Coeff q ⧸ (fderiv ℂ F b).range)) ∧
        fderiv ℂ F 0 = (-2 : ℂ) • ContinuousLinearMap.id ℂ (Coeff q) ∧
        (∃ G : Coeff q → Coeff q, AnalyticAt ℂ G 0 ∧ G 0 = 0 ∧
          (∀ᶠ b in 𝓝 (0 : Coeff q), G (F b) = b) ∧
          (∀ᶠ c in 𝓝 (0 : Coeff q), F (G c) = c) ∧
          fderiv ℂ G 0 = (-2 : ℂ)⁻¹ • ContinuousLinearMap.id ℂ (Coeff q)) ∧
        ∃ O : Set (Coeff q), IsOpen O ∧ O ⊆ V ∧ V ⊆ closure O ∧
          ∀ b ∈ O, IsUnit (fderiv ℂ F b) ∧
            ∃ G : Coeff q → Coeff q, AnalyticAt ℂ G (F b) ∧ G (F b) = b ∧
              (∀ᶠ c in 𝓝 b, G (F c) = c) ∧
              (∀ᶠ z in 𝓝 (F b), F (G z) = z) ∧
              fderiv ℂ G (F b) = Ring.inverse (fderiv ℂ F b) := by
  obtain ⟨hp1,W,s,A,P,hs,W₀,B,X,t,D,V,hV,hzero,hcenter,hpos,himage,F,hF,hFR,hFzero,hrec,hFred,hd,hG⟩ :=
    exists_sourceFrequency_localInverse (q := q) hp hp2
  let V' := connectedComponentIn V (0 : Coeff q)
  have hV' : IsOpen V' := hV.connectedComponentIn
  have hsub : V' ⊆ V := connectedComponentIn_subset V 0
  have hz' : (0 : Coeff q) ∈ V' := mem_connectedComponentIn hzero
  have hcenter' := D.real_actions_mem_zero_component hcenter
  have hpos' := nonnegative_summable_actions_mem_zero_component hpos
  have himage' : ∃ Y : Set (CoeffPair p), IsOpen Y ∧ realTypeSourceLocus p ⊆ Y ∧ Y ⊆ X ∧
      sourceActionSequence (q := q) hp hp1 t '' Y = V' := by
    obtain ⟨Y,hY,hrealY,hYX,hIY⟩ := himage
    let I := sourceActionSequence (q := q) hp hp1 t
    refine ⟨Y ∩ I ⁻¹' V',
      (D.actionSequence_analytic.continuousOn.mono hYX).isOpen_inter_preimage hY hV',?_,
      fun _ hψ => hYX hψ.1,?_⟩
    · intro ψ hψ
      exact ⟨hrealY hψ,hcenter' ⟨ψ,hψ⟩⟩
    · ext b
      constructor
      · rintro ⟨ψ,hψ,rfl⟩
        exact hψ.2
      · intro hb
        obtain ⟨ψ,hψ,he⟩ := hIY.symm ▸ hsub hb
        exact ⟨ψ,⟨hψ,by simpa only [mem_preimage,I,he] using! hb⟩,he⟩
  have hu0 : IsUnit (fderiv ℂ F 0) := by
    rw [hd,ContinuousLinearMap.isUnit_iff_bijective]
    exact (LinearEquiv.smulOfNeZero ℂ (Coeff q) (-2) (by norm_num)).bijective
  have hcompact : ∀ b ∈ V', IsCompactOperator (fderiv ℂ F b - (-2 : ℂ) • 1 : Coeff q →L[ℂ] Coeff q) := by
    intro b hb
    rw [neg_smul,sub_neg_eq_add]
    convert (hFred b (hsub hb)).1 using 1
    congr 1
  obtain ⟨hO,hDense⟩ := CompactSpectrum.open_dense_isUnit_of_analytic_compact_shift
    hV' isPreconnected_connectedComponentIn (hF.fderiv.mono hsub) (by norm_num : (-2 : ℂ) ≠ 0)
    hcompact ⟨0,hz',hu0⟩
  refine ⟨hp1,W,s,A,P,hs,W₀,B,X,t,D,V',hV',isPreconnected_connectedComponentIn,hz',hcenter',hpos',
    himage',F,hF.mono hsub,hFR.mono hsub,hFzero,hrec,fun b hb => hFred b (hsub hb),hd,hG,
    {b ∈ V' | IsUnit (fderiv ℂ F b)},hO,fun _ hb => hb.1,hDense,?_⟩
  intro b hb
  exact ⟨hb.2,ComplexAnalysis.exists_localInverse_of_isUnit_fderiv (hF b (hsub hb.1)) hb.2⟩

end NLS.ZakharovShabat
