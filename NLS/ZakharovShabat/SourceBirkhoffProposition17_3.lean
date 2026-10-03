import NLS.ZakharovShabat.SourceHilbertFiniteActionReduction
import NLS.ZakharovShabat.SourceBirkhoffProposition17_2
import NLS.SequenceSpaces.RealActionTail

/-! # Proposition 17.3: surjectivity for exponents at most two

Take the Hilbert preimage of an arbitrary exponent-`p` target. Finitely
many actual angle-flow reductions put its output inside the small ball
already covered by the exponent-`p` local inverse. Hilbert injectivity
identifies the reduced source with that exponent-`p` preimage. Lemma 17.4
then recovers the original source in exponent `p` as well.
-/
noncomputable section
open Set Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}

/-- Proposition 17.3: every real sequence target is attained when `1 < p ≤ 2`. -/
theorem proposition17_3 (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (hp2 : p ≤ 2) : Function.Surjective (sourceRealBirkhoffMap hp hp1 s) := by
  obtain ⟨V₀,C,V,u,E⟩ :=
    exists_sourceBirkhoffMap_complex_analytic (p := 2) (by simp) (by norm_num)
  let f := sourceRealBirkhoffMap hp hp1 s
  let inc := (RealCoeff.exponentInclusion hp2).prodMap (RealCoeff.exponentInclusion hp2)
  have hinj : Function.Injective inc := by
    intro z w h
    exact Prod.ext
      (RealCoeff.exponentInclusion_injective hp2 (congrArg Prod.fst h))
      (RealCoeff.exponentInclusion_injective hp2 (congrArg Prod.snd h))
  have hz : f 0 = 0 := by
    apply hinj
    have h := D.real_map_exponent E hp2 (0 : realTypeSourceSubmodule p)
    have hi : realTypeSourceExponentInclusion hp2 (0 : realTypeSourceSubmodule p) =
        (0 : realTypeSourceSubmodule 2) := by
      apply Subtype.ext
      exact map_zero (CoeffPair.exponentInclusion hp2)
    rw [hi,(E.hilbert_real_map_eq_zero_iff 0).mpr rfl] at h
    exact h.trans (map_zero inc).symm
  have hopen : IsOpen (range f) := by
    simpa only [image_univ] using D.real_map_isOpenEmbedding.isOpenMap univ isOpen_univ
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hopen 0 ⟨0,hz⟩
  intro z
  let φ := E.hilbertRealHomeomorph.symm (inc z)
  have hout : E.hilbertRealHomeomorph φ = inc z := E.hilbertRealHomeomorph.apply_symm_apply _
  obtain ⟨A,δ,hδ,hcriterion⟩ := RealCoeff.exists_finite_action_small_norm hp z hε
  obtain ⟨moves,hm,_,hsmall,houtside,_⟩ :=
    E.exists_hilbertActionReductionSequence_small_actions φ A (fun _ => δ) (fun _ _ => hδ)
  let ψ := E.hilbertActionReductionSequence φ moves
  have htail (n : ℤ) (hn : n ∉ A) :
      (E.hilbertRealHomeomorph ψ).1 n = z.1 n ∧
      (E.hilbertRealHomeomorph ψ).2 n = z.2 n := by
    have he₁ := congrArg (fun v : RealCoeff 2 × RealCoeff 2 => v.1 n) hout
    have he₂ := congrArg (fun v : RealCoeff 2 × RealCoeff 2 => v.2 n) hout
    exact ⟨(houtside n hn).1.trans he₁,(houtside n hn).2.trans he₂⟩
  have hactions (n : ℤ) (hn : n ∈ A) :
      RealCoeff.pairAction (E.hilbertRealHomeomorph ψ) n < δ := by
    rw [E.hilbert_pairAction_eq]
    exact hsmall n hn
  obtain ⟨y,hy,hycoords⟩ := hcriterion (E.hilbertRealHomeomorph ψ) htail hactions
  have hyout : inc y = E.hilbertRealHomeomorph ψ := by
    apply Prod.ext <;> ext n
    · exact (hycoords n).1
    · exact (hycoords n).2
  obtain ⟨ψp,hψp⟩ := hball (by simpa only [Metric.mem_ball,dist_zero_right] using hy)
  have hψ : realTypeSourceExponentInclusion hp2 ψp = ψ := by
    apply E.hilbertRealHomeomorph.injective
    calc
      _ = inc (f ψp) := (D.real_map_exponent E hp2 ψp).symm
      _ = inc y := congrArg inc hψp
      _ = E.hilbertRealHomeomorph ψ := hyout
  obtain ⟨φp,hφp⟩ := (E.hilbertActionReductionSequence_mem_exponent_iff hp hp1 hp2 φ moves hm).mp
    ⟨ψp,congrArg Subtype.val hψ⟩
  refine ⟨φp,hinj ?_⟩
  have hφ : realTypeSourceExponentInclusion hp2 φp = φ := Subtype.ext hφp
  calc
    inc (f φp) = E.hilbertRealHomeomorph (realTypeSourceExponentInclusion hp2 φp) :=
      D.real_map_exponent E hp2 φp
    _ = E.hilbertRealHomeomorph φ := congrArg E.hilbertRealHomeomorph hφ
    _ = inc z := hout

end SourceBirkhoffMapComplexData

/-- A normalized family with a bijective actual real Birkhoff map is
constructed at every exponent `1 < p ≤ 2`. -/
theorem exists_sourceBirkhoffFamily_bijective (hp : p ≠ ⊤) (hp1 : 1 < p) (hp2 : p ≤ 2) :
    ∃ W₀ B W : Set (CoeffPair p), ∃ s : (k : ℤ) → CoeffPair p → DeletedCoeff p k,
      SourceBirkhoffMapComplexData hp hp1 W₀ B W s ∧
      Function.Bijective (sourceRealBirkhoffMap hp hp1 s) := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  exact ⟨W₀,B,W,s,D,D.proposition17_2,D.proposition17_3 hp2⟩

end NLS.ZakharovShabat
