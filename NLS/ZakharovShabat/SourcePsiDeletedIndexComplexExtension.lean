import NLS.ZakharovShabat.SourceLemma12_10
import NLS.ZakharovShabat.SourcePsiDeletedIndexEquation

/-!
# A common complex extension on literal retained indices

The actual Proposition 12.9 root maps extend on one open simply connected
complex neighborhood common to every omitted index. Exact index isometries
preserve analyticity, the original equation and real base values. Supplied
original disks retain all roots on one source ball independent of both indices.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The common complex branch is analytic on the literal retained-index space. -/
theorem SourceLemma12_10Data.deletedIndex_analytic
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_10Data hp hp1 W₀ W s) (n : ℤ) :
    AnalyticOnNhd ℂ (fun ψ => DeletedCoeff.indexEquiv hp n (s n ψ)) W := by
  intro ψ hψ
  exact ((DeletedCoeff.indexEquiv hp n).toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp
    (H.analytic n ψ hψ)

/-- Every retained-index branch solves the actual equation on the same common domain. -/
theorem SourceLemma12_10Data.deletedIndex_equation
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_10Data hp hp1 W₀ W s)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    sourcePsiDeletedIndexEquation hp hp1 n ψ (DeletedCoeff.indexEquiv hp n (s n ψ)) = 0 := by
  rw [sourcePsiDeletedIndexEquation_eq_zero_iff,
    (DeletedCoeff.indexEquiv hp n).symm_apply_apply]
  exact H.equation ψ hψ n

/-- The complex branch agrees exactly with the canonical real solution. -/
theorem SourceLemma12_10Data.deletedIndex_real_agreement
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_10Data hp hp1 W₀ W s)
    (n : ℤ) (φ : realTypeSourceSubmodule p) :
    DeletedCoeff.indexEquiv hp n (s n φ) = DeletedCoeff.indexEquiv hp n
      (RealDeletedCoeff.complexCLM n (sourcePsiOriginalRootReal hp hp1 n φ)) :=
  congrArg (DeletedCoeff.indexEquiv hp n) (H.real_agreement n φ)

/-- One source radius places every retained root in its supplied original disk. -/
theorem SourceLemma12_10Data.deletedIndex_original_placement
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}
    (H : SourceLemma12_10Data hp hp1 W₀ W s)
    {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ}
    (hD : SourceIsolatingNeighborhoods hp hp1 V D c) (hV : IsOpen V)
    (φ : realTypeSourceLocus p) (hφV : φ.val ∈ V) :
    ∃ δ : ℝ, 0 < δ ∧ ball φ.val δ ⊆ W ∩ V ∧
      ∀ ψ ∈ ball φ.val δ, ∀ n : ℤ, ∀ m : {m : ℤ // m ≠ n},
        (Real.pi:ℂ)*m.val+DeletedCoeff.indexEquiv hp n (s n ψ) m ∈ D m.val := by
  obtain ⟨δ,hδ,hsub,hplace⟩ := H.original_placement hD hV φ hφV
  refine ⟨δ,hδ,hsub,?_⟩
  intro ψ hψ n m
  exact hplace ψ hψ n m.val m.property

/-- All literal retained-index branches share one simply connected complex domain and original placement radii. -/
theorem SourceProposition12_9Data.exists_deletedIndex_complex_extension
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ : Set (CoeffPair p)}
    (H : SourceProposition12_9Data hp hp1 W₀)
    (hW₀ : IsOpen W₀) (hR : realTypeSourceLocus p ⊆ W₀) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsSimplyConnected W ∧
      realTypeSourceLocus p ⊆ W ∧ W ⊆ W₀ ∧
      ∃ s : (n : ℤ) → CoeffPair p → DeletedIndexCoeff p n,
        (∀ n : ℤ, AnalyticOnNhd ℂ (s n) W) ∧
        (∀ ψ ∈ W, ∀ n : ℤ, sourcePsiDeletedIndexEquation hp hp1 n ψ (s n ψ) = 0) ∧
        (∀ n : ℤ, ∀ φ : realTypeSourceSubmodule p,
          s n φ = DeletedCoeff.indexEquiv hp n
            (RealDeletedCoeff.complexCLM n (sourcePsiOriginalRootReal hp hp1 n φ))) ∧
        ∀ {V : Set (CoeffPair p)} {D : ℤ → Set ℂ} {c : ℝ},
          SourceIsolatingNeighborhoods hp hp1 V D c → IsOpen V →
          ∀ φ : realTypeSourceLocus p, φ.val ∈ V →
            ∃ δ : ℝ, 0 < δ ∧ ball φ.val δ ⊆ W ∩ V ∧
              ∀ ψ ∈ ball φ.val δ, ∀ n : ℤ, ∀ m : {m : ℤ // m ≠ n},
                (Real.pi:ℂ)*m.val+s n ψ m ∈ D m.val := by
  obtain ⟨W,hW,hWconn,hRW,s,Hs⟩ := H.lemma12_10 hW₀ hR
  refine ⟨W,hW,hWconn,hRW,Hs.subset,
    (fun n ψ => DeletedCoeff.indexEquiv hp n (s n ψ)),
    Hs.deletedIndex_analytic,Hs.deletedIndex_equation,Hs.deletedIndex_real_agreement,?_⟩
  exact fun hD hV φ hφV => Hs.deletedIndex_original_placement hD hV φ hφV

end NLS.ZakharovShabat
