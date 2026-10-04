import NLS.SequenceSpaces.BoundedRealActionBallGluing
import NLS.ZakharovShabat.SourceFrequencyRealActionBalls
import NLS.ZakharovShabat.SourcePositiveActionRealization

/-! # Global analytic frequency maps with bounds on fixed action balls

The actual local frequency and refined correction maps glue on the union
of their action balls. This is one open complex neighborhood of all real
source actions, including the nonnegative summable cone, and serves all
admissible target exponents simultaneously. Each correction target retains
a norm bound on every original ball of this fixed cover.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- The actual frequency and refined correction extend analytically to one
open action domain with a fixed ball cover carrying simultaneous refined
correction bounds. Every real source has exact recovery. -/
theorem exists_sourceFrequency_boundedActionSpace_maps (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p) :
    ∃ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
    ∃ P : Set (CoeffPair p), SourcePsiIsolatingComplexExtension hp hp1 P s ∧
    ∃ W₀ B X : Set (CoeffPair p), ∃ t : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ _D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t,
    ∃ V : Set (Coeff q), ∃ ρ : realTypeSourceSubmodule p → ℝ,
      (∀ φ, 0 < ρ φ) ∧
      V = ⋃ φ, ball (sourceActionSequence (q := q) hp hp1 t φ.val) (ρ φ) ∧
      IsOpen V ∧
      (∀ φ : realTypeSourceSubmodule p, sourceActionSequence (q := q) hp hp1 t φ.val ∈ V) ∧
      (∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) →
        Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) ∈ V) ∧
      (∀ b ∈ V, ∃ ψ ∈ X, sourceActionSequence (q := q) hp hp1 t ψ = b) ∧
      (∃ Y : Set (CoeffPair p), IsOpen Y ∧ realTypeSourceLocus p ⊆ Y ∧ Y ⊆ X ∧
        sourceActionSequence (q := q) hp hp1 t '' Y = V) ∧
      (∀ f g : Coeff q → ℂ, AnalyticOnNhd ℂ f V → AnalyticOnNhd ℂ g V →
        (∀ ψ : realTypeSourceSubmodule p, f (sourceActionSequence (q := q) hp hp1 t ψ.val) =
          g (sourceActionSequence (q := q) hp hp1 t ψ.val)) → EqOn f g V) ∧
      (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
        ∃ F : Coeff q → Coeff r, AnalyticOnNhd ℂ F V ∧
          ∀ ψ : realTypeSourceSubmodule p,
            F (sourceActionSequence (q := q) hp hp1 t ψ.val) = A.frequencySequence r ψ.val ∧
            ∀ n, F (sourceActionSequence (q := q) hp hp1 t ψ.val) n = A.renormalizedFrequency n ψ.val) ∧
      (∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/3) ≤ r →
        ∃ H : Coeff q → Coeff r, AnalyticOnNhd ℂ H V ∧
          (∀ ψ : realTypeSourceSubmodule p,
            H (sourceActionSequence (q := q) hp hp1 t ψ.val) = A.actionFrequencyCorrectionSequence r ψ.val ∧
            ∀ n, H (sourceActionSequence (q := q) hp hp1 t ψ.val) n =
              A.renormalizedFrequency n ψ.val+2*sourceActionSequence (q := q) hp hp1 t ψ.val n) ∧
          ∀ φ, ∃ M : ℝ, 0 ≤ M ∧ ∀ b ∈ ball (sourceActionSequence (q := q) hp hp1 t φ.val) (ρ φ), ‖H b‖ ≤ M) := by
  classical
  obtain ⟨W,s,A,P,hs,W₀,B,X,t,D,hfreqval,hcorrval,hballs⟩ :=
    exists_sourceFrequency_boundedRealActionBalls (q := q) hp hp1
  choose R hR hcomplex hreal hfreq hcorr using hballs
  let a : realTypeSourceSubmodule p → Coeff q := fun φ => sourceActionSequence hp hp1 t φ.val
  let V := ⋃ φ, ball (a φ) (R φ)
  have ha (φ : realTypeSourceSubmodule p) : a φ ∈ Coeff.nonnegativeLocus q :=
    D.actionSequence_mem_nonnegativeLocus φ
  have hcenter (φ : realTypeSourceSubmodule p) : a φ ∈ V :=
    mem_iUnion.mpr ⟨φ,mem_ball_self (hR φ)⟩
  refine ⟨W,s,A,P,hs,W₀,B,X,t,D,V,R,hR,rfl,isOpen_iUnion (fun _ => isOpen_ball),hcenter,?_,?_,?_,?_,?_,?_⟩
  · intro b hb
    obtain ⟨φ,hφ⟩ := exists_source_of_nonnegative_actions hp hp1 h2p b hb
    have he : a φ = Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) := by
      ext n
      exact (D.actionSequence_apply φ.val (D.real_subset φ.property) n).trans (hφ n)
    rw [← he]
    exact hcenter φ
  · intro b hb
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hb
    exact hcomplex φ b hφ
  · let Y := X ∩ sourceActionSequence (q := q) hp hp1 t ⁻¹' V
    refine ⟨Y, D.actionSequence_analytic.continuousOn.isOpen_inter_preimage
      D.source_open (isOpen_iUnion (fun _ => isOpen_ball)), ?_, inter_subset_left, ?_⟩
    · intro ψ hψ
      exact ⟨D.real_subset hψ, hcenter ⟨ψ,hψ⟩⟩
    · apply Subset.antisymm
      · rintro b ⟨ψ,hψ,rfl⟩
        exact hψ.2
      · intro b hb
        obtain ⟨φ,hφ⟩ := mem_iUnion.mp hb
        obtain ⟨ψ,hψ,he⟩ := hcomplex φ b hφ
        exact ⟨ψ,⟨hψ,show sourceActionSequence (q := q) hp hp1 t ψ ∈ V from he.symm ▸ hb⟩,he⟩
  · intro f g hf hg he
    exact Coeff.eqOn_of_real_action_ball_agreement hp a R ha hR hreal f g hf hg he
  · intro r inst hr hr1 hpr
    obtain ⟨F,hF,hrec⟩ := Coeff.exists_analytic_gluing_of_real_action_ball_recovery hp a R
      (fun φ => A.frequencySequence r φ.val) ha hR hreal (fun φ => hfreq φ r hr hr1 hpr)
    exact ⟨F,hF,fun ψ => ⟨hrec ψ,fun n => by rw [hrec ψ]; exact hfreqval r hr hr1 hpr ψ n⟩⟩
  · intro r inst hr hr1 hpr
    obtain ⟨H,hH,hrec,hbound⟩ := Coeff.exists_bounded_analytic_gluing_of_real_action_ball_recovery hp a R
      (fun φ => A.actionFrequencyCorrectionSequence r φ.val) ha hR hreal (fun φ => hcorr φ r hr hr1 hpr)
    exact ⟨H,hH,fun ψ => ⟨hrec ψ,fun n => by rw [hrec ψ]; exact hcorrval r hr hr1 hpr ψ n⟩,hbound⟩

end NLS.ZakharovShabat
