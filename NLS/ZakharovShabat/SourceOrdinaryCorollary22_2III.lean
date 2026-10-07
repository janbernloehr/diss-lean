import NLS.ZakharovShabat.SourceOrdinarySourceObstruction
import NLS.ZakharovShabat.SourceOrdinaryFlowExistence

/-! # Corollary 22.2(iii) for the constructed ordinary spectral flow

Every extension of the Hilbert ordinary flow to p ≥ 2 fails continuity
at each source outside the Hilbert locus, in C([-T,T], source q) for every
finite q ≥ p and T > 0. The source and target atlases are constructed,
not extra hypotheses. Agreement with classical PDE solutions is separate.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
variable {W₂ P₂ : Set (CoeffPair 2)} {s₂ : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
variable {V₂ B₂ X₂ : Set (CoeffPair 2)} {t₂ : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}

/-- Corollary 22.2(iii): no compact-time source extension at a non-Hilbert point,
even in any weaker finite-exponent target norm. -/
theorem SourceAbelianMomentAtlas.corollary22_2_iii
    (H : SourceAbelianMomentAtlas (by simp) (by norm_num) W₂ s₂)
    (hs₂ : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P₂ s₂)
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₂ B₂ X₂ t₂)
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤) (hq1 : 1 < q)
    (h2p : 2 ≤ p) (hpq : p ≤ q) (T : ℝ) (hT : 0 < T)
    (φ : realTypeSourceSubmodule p) (hφ : φ ∉ sourceHilbertLocus h2p)
    (F : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule q))
    (he : ∀ ψ : realTypeSourceSubmodule 2, ∀ τ : Icc (-T) T,
      F (realTypeSourceExponentInclusion h2p ψ) τ =
        realTypeSourceExponentInclusion (h2p.trans hpq) (H.ordinarySourceFlow E le_rfl ψ τ.val)) :
    ¬ ContinuousAt F φ := by
  intro hF
  obtain ⟨W,P,_,_,hP,hr,s,hs,⟨A⟩⟩ := exists_sourceAbelianMoment_squaredGapAtlas hp hp1
  obtain ⟨V,B,X,t,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  obtain ⟨Vq,Bq,Xq,tq,Q⟩ := exists_sourceBirkhoffMap_complex_analytic hq hq1
  let r : C(Icc (0 : ℝ) T,Icc (-T) T) :=
    ⟨fun τ => ⟨τ.val,by constructor; linarith [τ.property.1]; exact τ.property.2⟩,
      by fun_prop⟩
  apply A.not_continuousAt_ordinarySource_extension hs hP hr D H hs₂ E Q h2p (h2p.trans hpq)
    T hT φ hφ (fun ψ => (F ψ).comp r) (fun ψ hf τ => ?_)
    ((ContinuousMap.continuous_precomp r).continuousAt.comp hF)
  have hi : (realTypeSourceExponentInclusion h2p (sourceFiniteGapHilbertModel hp hp1 ψ hf) :
      realTypeSourceSubmodule p) = ψ := sourceFiniteGapHilbertModel_inclusion hp hp1 h2p ψ hf
  have he' := he (sourceFiniteGapHilbertModel hp hp1 ψ hf) (r τ)
  rw [hi] at he'
  exact he'

/-- A continuous extension on the entire source space is impossible as soon as it
contains a non-Hilbert point. -/
theorem SourceAbelianMomentAtlas.not_continuous_ordinarySource_extension
    (H : SourceAbelianMomentAtlas (by simp) (by norm_num) W₂ s₂)
    (hs₂ : SourcePsiIsolatingComplexExtension (by simp) (by norm_num) P₂ s₂)
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₂ B₂ X₂ t₂)
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤) (hq1 : 1 < q)
    (h2p : 2 ≤ p) (hpq : p ≤ q) (T : ℝ) (hT : 0 < T)
    (hnon : ∃ φ : realTypeSourceSubmodule p, φ ∉ sourceHilbertLocus h2p)
    (F : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule q))
    (he : ∀ ψ : realTypeSourceSubmodule 2, ∀ τ : Icc (-T) T,
      F (realTypeSourceExponentInclusion h2p ψ) τ =
        realTypeSourceExponentInclusion (h2p.trans hpq) (H.ordinarySourceFlow E le_rfl ψ τ.val)) :
    ¬ Continuous F := by
  intro hF
  obtain ⟨φ,hφ⟩ := hnon
  exact H.corollary22_2_iii hs₂ E hp hp1 hq hq1 h2p hpq T hT φ hφ F he hF.continuousAt

/-- The constructed analytic Hilbert trajectories satisfy the nonextension result,
with no atlas or Birkhoff data supplied by the caller. -/
theorem exists_ordinarySourceTrajectories_with_nonextension
    (hp : p ≠ ⊤) (hp1 : 1 < p) (hq : q ≠ ⊤) (hq1 : 1 < q)
    (h2p : 2 ≤ p) (hpq : p ≤ q) (T : ℝ) (hT : 0 < T) :
    ∃ S : realTypeSourceSubmodule 2 → C(Icc (-T) T,realTypeSourceSubmodule 2),
      AnalyticOnNhd ℝ S univ ∧
      ∀ F : realTypeSourceSubmodule p → C(Icc (-T) T,realTypeSourceSubmodule q),
        (∀ ψ : realTypeSourceSubmodule 2, ∀ τ : Icc (-T) T,
          F (realTypeSourceExponentInclusion h2p ψ) τ =
            realTypeSourceExponentInclusion (h2p.trans hpq) (S ψ τ)) →
        ∀ φ : realTypeSourceSubmodule p, φ ∉ sourceHilbertLocus h2p → ¬ ContinuousAt F φ := by
  obtain ⟨W,P,s,H,hs,hP,hr,V,B,X,t,E,hA,_⟩ :=
    exists_analytic_ordinarySourceTrajectories (p := 2) (by simp) (by norm_num) le_rfl
  refine ⟨H.ordinarySourceTrajectoryOn hs hP hr E le_rfl T,hA T,?_⟩
  intro F he φ hφ
  exact H.corollary22_2_iii hs.toSourcePsiIsolatingComplexExtension E
    hp hp1 hq hq1 h2p hpq T hT φ hφ F he

end NLS.ZakharovShabat
