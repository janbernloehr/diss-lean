import NLS.ZakharovShabat.SourceFrequencyOriginalPhysical
import NLS.SequenceSpaces.NonnegativeAnalyticDensity

/-!
# Restricting and identifying original action frequencies

The original spectral values determine the full analytic map on the common
connected action domain. Restricting that domain retains all frequency data.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W V : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
  {D : SourceSection17OriginalData hp hp1 W₀ W V s}
  {U : Set (Coeff q)} {F : Coeff q → Coeff q}

/-- Actual spectral recovery identifies the two maps on their common zero component. -/
theorem SourceOriginalFrequencyData.eqOn_component_of_original_recovery
    (E : SourceOriginalFrequencyData D U F) (h2p : 2 ≤ p)
    {Wa P : Set (CoeffPair p)} {sa : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (A : SourceAbelianMomentAtlas hp hp1 Wa sa)
    (hs : SourcePsiIsolatingComplexExtension hp hp1 P sa)
    (T : Set (Coeff q)) (hT : IsOpen T) (G : Coeff q → Coeff q)
    (hG : AnalyticOnNhd ℂ G T)
    (hcenter : ∀ φ : realTypeSourceSubmodule p, sourceActionSequence hp hp1 s φ.val ∈ T)
    (hrec : ∀ φ : realTypeSourceSubmodule p, ∀ n,
      G (sourceActionSequence hp hp1 s φ.val) n = A.renormalizedFrequency n φ.val) :
    EqOn F G (connectedComponentIn (U ∩ T) 0) := by
  obtain ⟨Wb,sb,B,Q,ht,hrecB⟩ := E.spectral
  have hpos (b : RealCoeff 1) (hb : ∀ n, 0 ≤ b n) :
      F (Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b)) =
        G (Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b)) := by
    ext n
    exact B.actionMap_eq_on_nonnegative_summable A ht hs D.complex D.complex h2p h2p
      (fun c k => F c k) (fun c k => G c k) hrecB hrec b hb n
  have hcone (b : Coeff q) (hb : b ∈ U ∩ T) (hbpos : b ∈ Coeff.nonnegativeLocus q) : F b = G b := by
    let a := Coeff.reCLM q b
    have ha : RealCoeff.complexCLM q a = b := RealCoeff.complexCLM_reCLM q b (fun n => (hbpos n).1)
    have hanonneg : ∀ n, 0 ≤ a n := fun n => (hbpos n).2
    have htend := RealCoeff.tendsto_complex_finiteSummable (Coeff.doublingExponent_ne_top hp) a
    rw [ha] at htend
    have hf := (E.analytic b hb.1).continuousAt.tendsto.comp htend
    have hg := (hG b hb.2).continuousAt.tendsto.comp htend
    have he : (fun S : Finset ℤ => F (Coeff.exponentInclusion (Fact.out : 1 ≤ q)
        (RealCoeff.complexCLM 1 (RealCoeff.finiteSummable S a)))) =
        (fun S : Finset ℤ => G (Coeff.exponentInclusion (Fact.out : 1 ≤ q)
          (RealCoeff.complexCLM 1 (RealCoeff.finiteSummable S a)))) := by
      funext S
      exact hpos _ (RealCoeff.finiteSummable_nonneg S a hanonneg)
    simp only [Function.comp_def] at hf hg
    rw [he] at hf
    exact tendsto_nhds_unique hf hg
  have hzT : (0 : Coeff q) ∈ T := by
    simpa only [ZeroMemClass.coe_zero,D.complex.actionSequence_zero] using hcenter 0
  have hz : (0 : Coeff q) ∈ U ∩ T := ⟨E.zero_mem,hzT⟩
  have hgerm := Coeff.eventuallyEq_of_nonnegative_agreement (Coeff.doublingExponent_ne_top hp)
    F G (U ∩ T) (E.isOpen.inter hT) 0 hz (Coeff.zero_mem_nonnegativeLocus q)
    (E.analytic.mono inter_subset_left).differentiableOn
    (hG.mono inter_subset_right).differentiableOn hcone
  have hsub : connectedComponentIn (U ∩ T) (0 : Coeff q) ⊆ U ∩ T := connectedComponentIn_subset _ _
  exact (E.analytic.mono (fun _ hb => (hsub hb).1)).eqOn_of_preconnected_of_eventuallyEq
    (hG.mono (fun _ hb => (hsub hb).2)) isPreconnected_connectedComponentIn
    (mem_connectedComponentIn hz) hgerm

/-- An open connected restriction retaining all real actions retains every
frequency conclusion, including its original source-image representation. -/
theorem SourceOriginalFrequencyData.restrict
    (E : SourceOriginalFrequencyData D U F) (h2p : 2 ≤ p)
    (T : Set (Coeff q)) (hT : IsOpen T) (hconn : IsPreconnected T)
    (hTU : T ⊆ U)
    (hcenter : ∀ φ : realTypeSourceSubmodule p, sourceActionSequence hp hp1 s φ.val ∈ T) :
    SourceOriginalFrequencyData D T F := by
  have hz : (0 : Coeff q) ∈ T := by
    simpa only [ZeroMemClass.coe_zero,D.complex.actionSequence_zero] using hcenter 0
  refine ⟨hT,hconn,hz,hcenter,?_,?_,E.analytic.mono hTU,E.map_zero,E.spectral,?_,?_⟩
  · intro b hb
    obtain ⟨φ,hφ⟩ := exists_source_of_nonnegative_actions hp hp1 h2p b hb
    have he : sourceActionSequence (q := q) hp hp1 s φ.val =
        Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) := by
      ext n
      exact (D.complex.actionSequence_apply φ.val (D.complex.real_subset φ.property) n).trans (hφ n)
    rw [← he]
    exact hcenter φ
  · obtain ⟨Y,hY,hrY,hYV,himage⟩ := E.source_image
    refine ⟨Y ∩ sourceActionSequence (q := q) hp hp1 s ⁻¹' T,
      (D.complex.actionSequence_analytic.continuousOn.mono hYV).isOpen_inter_preimage hY hT,
      fun φ hφ => ⟨hrY hφ,hcenter ⟨φ,hφ⟩⟩,fun _ hφ => hYV hφ.1,?_⟩
    apply Subset.antisymm
    · rintro _ ⟨φ,hφ,rfl⟩
      exact hφ.2
    · intro b hb
      obtain ⟨φ,hφ,he⟩ := himage.symm ▸ hTU hb
      exact ⟨φ,⟨hφ,show sourceActionSequence (q := q) hp hp1 s φ ∈ T from he.symm ▸ hb⟩,he⟩
  · intro r inst hr hr1 hpr
    obtain ⟨H,hH,hHR,hval⟩ := E.refined r hr hr1 hpr
    exact ⟨H,hH.mono hTU,hHR.mono hTU,fun b hb => hval b (hTU hb)⟩
  · intro b hb
    obtain ⟨L,hL,hbL,_,g,h,hval,⟨M,hM,hbound⟩,hplus⟩ := E.mixed b (hTU hb)
    refine ⟨L ∩ T,hL.inter hT,⟨hbL,hb⟩,inter_subset_right,g,h,
      fun c hc => hval c hc.1,⟨M,hM,fun c hc => hbound c hc.1⟩,?_⟩
    intro r hr1 hr
    obtain ⟨K,hK,hKbound⟩ := hplus r hr1 hr
    exact ⟨K,hK,fun c hc => hKbound c hc.1⟩

end NLS.ZakharovShabat
