import NLS.ZakharovShabat.SourceBirkhoffFiniteGapFibers
import NLS.ZakharovShabat.SourceBirkhoffMapExponent

/-! # Reduction of global Birkhoff injectivity to the Hilbert case

Every collision at any finite exponent above one gives an actual Hilbert
collision. Above two, first approximate it by a finite-gap collision and
use the proved Hilbert realizations. Below two, use direct inclusion.
Hilbert global injectivity is an explicit premise, not an axiom or a
consequence of local invertibility.
-/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (k : ℤ) → CoeffPair p → DeletedCoeff p k}
  {V₀ C V : Set (CoeffPair 2)} {t : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- A finite-gap collision above two has distinct coefficient-preserving
Hilbert preimages with the same actual Hilbert Birkhoff output. -/
theorem exists_hilbert_preimages_of_finiteGap_collision
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₀ C V t)
    (h2p : (2 : ℝ≥0∞) ≤ p)
    (φ ψ : realTypeSourceSubmodule p)
    (hfφ : φ ∈ sourceFiniteGapLocus hp hp1) (hfψ : ψ ∈ sourceFiniteGapLocus hp hp1)
    (hne : φ ≠ ψ)
    (heq : sourceRealBirkhoffMap hp hp1 s φ = sourceRealBirkhoffMap hp hp1 s ψ) :
    ∃ u v : realTypeSourceSubmodule 2,
      CoeffPair.exponentInclusion h2p u.val = φ.val ∧
      CoeffPair.exponentInclusion h2p v.val = ψ.val ∧ u ≠ v ∧
      sourceRealBirkhoffMap (by simp) (by norm_num) t u =
        sourceRealBirkhoffMap (by simp) (by norm_num) t v := by
  obtain ⟨u, hu, hru, _⟩ := sourceFiniteGap_exists_hilbert_realization hp hp1 h2p φ hfφ
  obtain ⟨v, hv, hrv, _⟩ := sourceFiniteGap_exists_hilbert_realization hp hp1 h2p ψ hfψ
  let u' : realTypeSourceSubmodule 2 := ⟨u,hru⟩
  let v' : realTypeSourceSubmodule 2 := ⟨v,hrv⟩
  have hue : (realTypeSourceExponentInclusion h2p u' : realTypeSourceSubmodule p) = φ := Subtype.ext hu
  have hve : (realTypeSourceExponentInclusion h2p v' : realTypeSourceSubmodule p) = ψ := Subtype.ext hv
  have hune : u' ≠ v' := by
    intro h
    apply hne
    exact hue.symm.trans ((congrArg (fun w : realTypeSourceSubmodule 2 =>
      (realTypeSourceExponentInclusion h2p w : realTypeSourceSubmodule p)) h).trans hve)
  have huout := (E.real_map_exponent D h2p u').trans
    (congrArg (sourceRealBirkhoffMap hp hp1 s) hue)
  have hvout := (E.real_map_exponent D h2p v').trans
    (congrArg (sourceRealBirkhoffMap hp hp1 s) hve)
  have hout := huout.trans (heq.trans hvout.symm)
  refine ⟨u',v',hu,hv,hune,?_⟩
  apply Prod.ext
  · exact RealCoeff.exponentInclusion_injective h2p (congrArg Prod.fst hout)
  · exact RealCoeff.exponentInclusion_injective h2p (congrArg Prod.snd hout)

/-- Every actual collision at any finite exponent above one induces an
actual collision for any constructed Hilbert Birkhoff family. -/
theorem exists_hilbert_collision_of_collision
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₀ C V t)
    (φ ψ : realTypeSourceSubmodule p) (hne : φ ≠ ψ)
    (heq : sourceRealBirkhoffMap hp hp1 s φ = sourceRealBirkhoffMap hp hp1 s ψ) :
    ∃ u v : realTypeSourceSubmodule 2, u ≠ v ∧
      sourceRealBirkhoffMap (by simp) (by norm_num) t u =
        sourceRealBirkhoffMap (by simp) (by norm_num) t v := by
  by_cases h2p : (2 : ℝ≥0∞) ≤ p
  · obtain ⟨S,φ',ψ',_,_,hne',hfφ,hfψ,hφ',hψ'⟩ :=
      D.exists_finiteGap_collision_mem_open φ ψ hne heq univ univ
        isOpen_univ isOpen_univ (mem_univ _) (mem_univ _)
    obtain ⟨u,v,_,_,huv,hout⟩ := D.exists_hilbert_preimages_of_finiteGap_collision E h2p
      φ' ψ' hfφ hfψ hne' (hφ'.trans hψ'.symm)
    exact ⟨u,v,huv,hout⟩
  · have hp2 : p ≤ 2 := le_of_not_ge h2p
    refine ⟨realTypeSourceExponentInclusion hp2 φ, realTypeSourceExponentInclusion hp2 ψ, ?_, ?_⟩
    · intro h
      apply hne
      apply Subtype.ext
      apply CoeffPair.exponentInclusion_injective hp2
      exact congrArg Subtype.val h
    · exact (D.real_map_exponent E hp2 φ).symm.trans
        ((congrArg ((RealCoeff.exponentInclusion hp2).prodMap (RealCoeff.exponentInclusion hp2)) heq).trans
          (D.real_map_exponent E hp2 ψ))

/-- The exponent-extension step of Proposition 17.2. Global Hilbert
injectivity is the only remaining injectivity premise. -/
theorem real_map_injective_of_hilbert
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₀ C V t)
    (hinj : Function.Injective (sourceRealBirkhoffMap (by simp) (by norm_num) t)) :
    Function.Injective (sourceRealBirkhoffMap hp hp1 s) := by
  intro φ ψ heq
  by_contra hne
  obtain ⟨u,v,huv,hout⟩ := D.exists_hilbert_collision_of_collision E φ ψ hne heq
  exact huv (hinj hout)

/-- It is enough to establish the missing Hilbert theorem on finite-gap sources. -/
theorem real_map_injective_of_hilbert_finiteGap
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₀ C V t)
    (hinj : Set.InjOn (sourceRealBirkhoffMap (by simp) (by norm_num) t)
      (sourceFiniteGapLocus (by simp) (by norm_num))) :
    Function.Injective (sourceRealBirkhoffMap hp hp1 s) :=
  D.real_map_injective_of_hilbert E (E.real_map_injective_iff_injOn_finiteGap.mpr hinj)

/-- Above two the global injectivity questions for any two constructed
families are equivalent, not merely related in one direction. -/
theorem real_map_injective_iff_hilbert_of_two_le
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (E : SourceBirkhoffMapComplexData (by simp) (by norm_num) V₀ C V t)
    (h2p : (2 : ℝ≥0∞) ≤ p) :
    Function.Injective (sourceRealBirkhoffMap hp hp1 s) ↔
      Function.Injective (sourceRealBirkhoffMap (by simp) (by norm_num) t) :=
  ⟨fun hi => E.real_map_injective_of_exponent D h2p hi, D.real_map_injective_of_hilbert E⟩

end SourceBirkhoffMapComplexData
end NLS.ZakharovShabat
