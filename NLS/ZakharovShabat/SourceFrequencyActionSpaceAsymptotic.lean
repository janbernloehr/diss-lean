import NLS.ZakharovShabat.SourceFrequencyBoundedActionSpaceMaps
import NLS.SequenceSpaces.ActionCorrectionIdentity
import NLS.SequenceSpaces.RefinedOnePlusDecomposition

/-! # Locally uniform mixed remainders on action space

The fixed action-ball cover carries every refined target bound. On each
ball, the correction has one l(p/3) + l(1+) decomposition, chosen before
all projection exponents and uniformly bounded there. This includes the
quasi-normed l(p/3) range below one.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- Actual analytic action frequencies with the literal locally uniform
mixed remainder, on a common action image containing the positive l1 cone. -/
theorem exists_sourceFrequency_actionSpace_asymptotic (hp : p ≠ ⊤) (hp1 : 1 < p) (h2p : 2 ≤ p) :
    ∃ W : Set (CoeffPair p), ∃ s : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ A : SourceAbelianMomentAtlas hp hp1 W s,
    ∃ P : Set (CoeffPair p), SourcePsiIsolatingComplexExtension hp hp1 P s ∧
    ∃ W₀ B X : Set (CoeffPair p), ∃ t : (n : ℤ) → CoeffPair p → DeletedCoeff p n,
    ∃ _D : SourceBirkhoffMapComplexData hp hp1 W₀ B X t,
    ∃ V : Set (Coeff q), IsOpen V ∧
      (∀ φ : realTypeSourceSubmodule p, sourceActionSequence (q := q) hp hp1 t φ.val ∈ V) ∧
      (∀ b : RealCoeff 1, (∀ n, 0 ≤ b n) →
        Coeff.exponentInclusion (Fact.out : 1 ≤ q) (RealCoeff.complexCLM 1 b) ∈ V) ∧
      (∃ Y : Set (CoeffPair p), IsOpen Y ∧ realTypeSourceLocus p ⊆ Y ∧ Y ⊆ X ∧
        sourceActionSequence (q := q) hp hp1 t '' Y = V) ∧
      ∀ (r : ℝ≥0∞) [Fact (1 ≤ r)], r ≠ ⊤ → 1 < r → ENNReal.ofReal (p.toReal/2) ≤ r →
        ∃ F : Coeff q → Coeff r, AnalyticOnNhd ℂ F V ∧ AnalyticOnNhd ℝ F V ∧
          (∀ ψ : realTypeSourceSubmodule p,
            F (sourceActionSequence (q := q) hp hp1 t ψ.val) = A.frequencySequence r ψ.val ∧
            ∀ n, F (sourceActionSequence (q := q) hp hp1 t ψ.val) n = A.renormalizedFrequency n ψ.val) ∧
          (∀ (u : ℝ≥0∞) [Fact (1 ≤ u)], u ≠ ⊤ → 1 < u → ENNReal.ofReal (p.toReal/3) ≤ u →
            ∃ H : Coeff q → Coeff u, AnalyticOnNhd ℂ H V ∧ AnalyticOnNhd ℝ H V ∧
              ∀ b ∈ V, ∀ n, H b n = F b n+2*b n) ∧
          ∀ b ∈ V, ∃ T : Set (Coeff q), IsOpen T ∧ b ∈ T ∧ T ⊆ V ∧
            (∀ u : ℝ≥0∞, u ≠ ⊤ → 1 < u → ENNReal.ofReal (p.toReal/3) ≤ u →
              ∃ M : ℝ, 0 ≤ M ∧ ∀ c ∈ T, ∃ w : Coeff u,
                (∀ n, w n = F c n+2*c n) ∧ ‖w‖ ≤ M) ∧
            ∃ g : Coeff q → Coeff (ENNReal.ofReal (p.toReal/3)), ∃ h : Coeff q → CoeffOnePlus,
              (∀ c ∈ T, ∀ n, F c n+2*c n = g c n+(h c).1 n) ∧
              (∃ M : ℝ, 0 ≤ M ∧ ∀ c ∈ T, ‖g c‖ ≤ M) ∧
              ∀ (u : ℝ≥0∞) (hu1 : 1 < u) (hu : u ≠ ⊤),
                ∃ M : ℝ, 0 ≤ M ∧ ∀ c ∈ T, ‖CoeffOnePlus.toCoeff u hu1 hu (h c)‖ ≤ M := by
  obtain ⟨W,s,A,P,hs,W₀,B,X,t,D,V,ρ,hρ,hcover,hV,hcenter,hpos,_,himage,huniq,hfreq,hcorr⟩ :=
    exists_sourceFrequency_boundedActionSpace_maps (q := q) hp hp1 h2p
  refine ⟨W,s,A,P,hs,W₀,B,X,t,D,V,hV,hcenter,hpos,himage,?_⟩
  intro r instR hr hr1 hpr
  obtain ⟨F,hF,hrec⟩ := hfreq r hr hr1 hpr
  have hfamily (u : ℝ≥0∞) [Fact (1 ≤ u)] (hu : u ≠ ⊤) (hu1 : 1 < u)
      (hpu : ENNReal.ofReal (p.toReal/3) ≤ u) :
      ∃ H : Coeff q → Coeff u, AnalyticOnNhd ℂ H V ∧
        (∀ b ∈ V, ∀ n, H b n = F b n+2*b n) ∧
        ∀ φ, ∃ M : ℝ, 0 ≤ M ∧ ∀ b ∈ ball (sourceActionSequence (q := q) hp hp1 t φ.val) (ρ φ), ‖H b‖ ≤ M := by
    obtain ⟨H,hH,hrecH,hbound⟩ := hcorr u hu hu1 hpu
    refine ⟨H,hH,?_,hbound⟩
    apply Coeff.actionCorrection_eq_of_analytic_uniqueness
      (fun ψ : realTypeSourceSubmodule p => sourceActionSequence hp hp1 t ψ.val) V huniq F H hF hH
    intro ψ n
    rw [(hrecH ψ).2 n,(hrec ψ).2 n]
  refine ⟨F,hF,hF.restrictScalars,hrec,?_,?_⟩
  · intro u instU hu hu1 hpu
    obtain ⟨H,hH,he,_⟩ := hfamily u hu hu1 hpu
    exact ⟨H,hH,hH.restrictScalars,he⟩
  · intro b hb
    rw [hcover] at hb
    obtain ⟨φ,hφ⟩ := mem_iUnion.mp hb
    let T := ball (sourceActionSequence (q := q) hp hp1 t φ.val) (ρ φ)
    have hTV : T ⊆ V := by
      intro c hc
      rw [hcover]
      exact mem_iUnion.mpr ⟨φ,hc⟩
    have hbound : ∀ u : ℝ≥0∞, u ≠ ⊤ → 1 < u → ENNReal.ofReal (p.toReal/3) ≤ u →
        ∃ M : ℝ, 0 ≤ M ∧ ∀ c ∈ T, ∃ w : Coeff u,
          (∀ n, w n = F c n+2*c n) ∧ ‖w‖ ≤ M := by
      intro u hu hu1 hpu
      let : Fact (1 ≤ u) := ⟨hu1.le⟩
      obtain ⟨H,_,he,hb⟩ := hfamily u hu hu1 hpu
      obtain ⟨M,hM,hn⟩ := hb φ
      exact ⟨M,hM,fun c hc => ⟨H c,he c (hTV hc),hn c hc⟩⟩
    exact ⟨T,isOpen_ball,hφ,hTV,hbound,
      Coeff.exists_onePlus_decomposition_of_refined T (fun c n => F c n+2*c n)
        ENNReal.ofReal_ne_top hbound⟩

end NLS.ZakharovShabat
