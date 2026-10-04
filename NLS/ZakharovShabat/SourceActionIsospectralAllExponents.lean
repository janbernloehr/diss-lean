import NLS.ZakharovShabat.SourceBirkhoffLemma17_5
import NLS.ZakharovShabat.SourceFiniteGapFrequencyExponent

/-! # Equal actions imply isospectrality at every finite exponent

Finite-gap sources are realized in the Hilbert space, where the full
action torus is isospectral. Independent local Birkhoff inverses then
lift matching finite truncations of any two equal-action sources.
Continuity of the discriminant passes the equality to their limits.
-/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The physical Hilbert model includes back to the original source. -/
theorem sourceFiniteGapHilbertModel_inclusion (hp : p ≠ ⊤) (hp1 : 1 < p)
    (h2p : 2 ≤ p) (φ : realTypeSourceSubmodule p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    realTypeSourceExponentInclusion h2p (sourceFiniteGapHilbertModel hp hp1 φ hf) = φ := by
  apply Subtype.ext
  apply (CoeffPair.toMax p).injective
  apply Prod.ext
  · ext n
    exact (sourceFiniteGapHilbertModel_coefficients hp hp1 φ hf n).1
  · ext n
    exact (sourceFiniteGapHilbertModel_coefficients hp hp1 φ hf n).2

/-- Equal actions of actual finite-gap sources imply equality of the
original spectrum and multiplicities at every finite p > 1. -/
theorem sourceFiniteGap_isospectral_of_actions (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p)
    (hf : φ ∈ sourceFiniteGapLocus hp hp1) (hg : ψ ∈ sourceFiniteGapLocus hp hp1)
    (ha : ψ ∈ sourceRealActionLevelSet hp hp1 φ) : ψ ∈ sourceIsospectralSet hp φ := by
  by_cases hp2 : p ≤ 2
  · exact sourceRealActionLevelSet_subset_isospectralSet hp hp1 hp2 φ ha
  have h2p : 2 ≤ p := (lt_of_not_ge hp2).le
  let φ₂ := sourceFiniteGapHilbertModel hp hp1 φ hf
  let ψ₂ := sourceFiniteGapHilbertModel hp hp1 ψ hg
  have hφ : realTypeSourceExponentInclusion h2p φ₂ = φ := sourceFiniteGapHilbertModel_inclusion hp hp1 h2p φ hf
  have hψ : realTypeSourceExponentInclusion h2p ψ₂ = ψ := sourceFiniteGapHilbertModel_inclusion hp hp1 h2p ψ hg
  have hφval : CoeffPair.exponentInclusion h2p φ₂.val = φ.val := congrArg Subtype.val hφ
  have hψval : CoeffPair.exponentInclusion h2p ψ₂.val = ψ.val := congrArg Subtype.val hψ
  have ha₂ : ψ₂ ∈ sourceRealActionLevelSet (by simp) (by norm_num) φ₂ := by
    intro n
    have heψ := congrArg Complex.re (sourceRealAction_exponent (by simp) hp (by norm_num) hp1 h2p n ψ₂)
    have heφ := congrArg Complex.re (sourceRealAction_exponent (by simp) hp (by norm_num) hp1 h2p n φ₂)
    change _ = (fun ξ : realTypeSourceSubmodule p => (sourceRealAction hp hp1 ξ.val ξ.property n).re)
      (realTypeSourceExponentInclusion h2p ψ₂) at heψ
    change _ = (fun ξ : realTypeSourceSubmodule p => (sourceRealAction hp hp1 ξ.val ξ.property n).re)
      (realTypeSourceExponentInclusion h2p φ₂) at heφ
    rw [hψ] at heψ
    rw [hφ] at heφ
    exact heψ.trans ((ha n).trans heφ.symm)
  have hi := sourceRealActionLevelSet_subset_isospectralSet (by simp) (by norm_num) (le_refl 2) φ₂ ha₂
  have he := (mem_sourceIsospectralSet_iff_discriminant_eq (by simp) (by norm_num) φ₂ ψ₂).mp hi
  apply (mem_sourceIsospectralSet_iff_discriminant_eq hp hp1 φ ψ).mpr
  funext z
  have hdψ := sourceDiscriminant_exponent (by simp) hp h2p ψ₂.val z
  have hdφ := sourceDiscriminant_exponent (by simp) hp h2p φ₂.val z
  rw [hψval] at hdψ
  rw [hφval] at hdφ
  exact hdψ.symm.trans ((congrFun he z).trans hdφ)

/-- Limits of pairs of isospectral sources remain isospectral. -/
theorem sourceIsospectralSet_of_tendsto_pair (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : realTypeSourceSubmodule p) (F G : Finset ℤ → realTypeSourceSubmodule p)
    (hF : Tendsto F atTop (𝓝 φ)) (hG : Tendsto G atTop (𝓝 ψ))
    (he : ∀ᶠ S in atTop, canonicalDiscriminant hp (periodOnePotential (G S).val) =
      canonicalDiscriminant hp (periodOnePotential (F S).val)) :
    ψ ∈ sourceIsospectralSet hp φ := by
  apply (mem_sourceIsospectralSet_iff_discriminant_eq hp hp1 φ ψ).mpr
  funext zeta
  have hd : Continuous (fun t : ℂ × CoeffPair p => canonicalDiscriminant hp (periodOnePotential t.2) t.1) :=
    continuousOn_univ.mp (analyticOnNhd_canonicalDiscriminant_periodOne hp hp1).continuousOn
  have hpair : Continuous (fun ξ : realTypeSourceSubmodule p => (zeta,ξ.val)) :=
    continuous_const.prodMk continuous_subtype_val
  have hc : Continuous (fun ξ : realTypeSourceSubmodule p => canonicalDiscriminant hp (periodOnePotential ξ.val) zeta) :=
    hd.comp (f := fun ξ : realTypeSourceSubmodule p => (zeta,ξ.val)) hpair
  have hezeta : ∀ᶠ S in atTop,
      canonicalDiscriminant hp (periodOnePotential (G S).val) zeta =
        canonicalDiscriminant hp (periodOnePotential (F S).val) zeta :=
    he.mono (fun _ h => congrFun h zeta)
  exact tendsto_nhds_unique (hc.continuousAt.tendsto.comp hG)
    ((hc.continuousAt.tendsto.comp hF).congr' (hezeta.mono (fun _ h => h.symm)))


namespace SourceBirkhoffMapComplexData
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ B W : Set (CoeffPair p)}
  {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Matching output truncations preserve equality of all original actions. -/
theorem actionLevelSet_of_equal_action_truncations
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s)
    (φ ψ φ' ψ' : realTypeSourceSubmodule p) (ha : ψ ∈ sourceRealActionLevelSet hp hp1 φ)
    (S : Finset ℤ)
    (hφ : sourceRealBirkhoffMap hp hp1 s φ' = RealCoeff.truncatePair S (sourceRealBirkhoffMap hp hp1 s φ))
    (hψ : sourceRealBirkhoffMap hp hp1 s ψ' = RealCoeff.truncatePair S (sourceRealBirkhoffMap hp hp1 s ψ)) :
    ψ' ∈ sourceRealActionLevelSet hp hp1 φ' := by
  intro n
  have he := (D.real_pairAction_eq ψ n).trans ((ha n).trans (D.real_pairAction_eq φ n).symm)
  rw [← D.real_pairAction_eq ψ' n,← D.real_pairAction_eq φ' n,hφ,hψ]
  by_cases hn : n ∈ S
  · simpa only [RealCoeff.pairAction,RealCoeff.truncatePair,RealCoeff.truncate_apply,if_pos hn] using he
  · simp only [RealCoeff.pairAction,RealCoeff.truncatePair,RealCoeff.truncate_apply,if_neg hn]

/-- Local inverse branches and finite truncations extend the action-to-spectrum
implication to all finite exponents, without assuming global surjectivity. -/
theorem actionLevelSet_subset_isospectralSet_all_exponents
    (D : SourceBirkhoffMapComplexData hp hp1 W₀ B W s) (φ : realTypeSourceSubmodule p) :
    sourceRealActionLevelSet hp hp1 φ ⊆ sourceIsospectralSet hp φ := by
  intro ψ ha
  obtain ⟨g,hg,hgφ,_,hrg,_⟩ := D.proposition17_1 φ
  obtain ⟨k,hk,hkψ,_,hrk,_⟩ := D.proposition17_1 ψ
  let z := sourceRealBirkhoffMap hp hp1 s φ
  let w := sourceRealBirkhoffMap hp hp1 s ψ
  let F := fun S : Finset ℤ => g (RealCoeff.truncatePair S z)
  let G := fun S : Finset ℤ => k (RealCoeff.truncatePair S w)
  have htφ := RealCoeff.tendsto_truncatePair hp z
  have htψ := RealCoeff.tendsto_truncatePair hp w
  have hF : Tendsto F atTop (𝓝 φ) := by
    have h := hg.continuousAt.tendsto.comp htφ
    rwa [hgφ] at h
  have hG : Tendsto G atTop (𝓝 ψ) := by
    have h := hk.continuousAt.tendsto.comp htψ
    rwa [hkψ] at h
  have he : ∀ᶠ S : Finset ℤ in atTop,
      canonicalDiscriminant hp (periodOnePotential (G S).val) =
        canonicalDiscriminant hp (periodOnePotential (F S).val) := by
    filter_upwards [htφ.eventually hrg,htψ.eventually hrk] with S hSφ hSψ
    have hf := D.finiteGap_of_real_map_eq_truncatePair (F S) S z hSφ
    have hg := D.finiteGap_of_real_map_eq_truncatePair (G S) S w hSψ
    exact (mem_sourceIsospectralSet_iff_discriminant_eq hp hp1 (F S) (G S)).mp
      (sourceFiniteGap_isospectral_of_actions hp hp1 (F S) (G S) hf hg
        (D.actionLevelSet_of_equal_action_truncations φ ψ (F S) (G S) ha S hSφ hSψ))
  exact sourceIsospectralSet_of_tendsto_pair hp hp1 φ ψ F G hF hG he

end SourceBirkhoffMapComplexData

/-- Equal actions characterize the actual isospectral sets throughout
all finite source exponents above one. The Birkhoff family is constructed. -/
theorem sourceIsospectralSet_eq_actionLevelSet_all_exponents
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) :
    sourceIsospectralSet hp φ = sourceRealActionLevelSet hp hp1 φ := by
  obtain ⟨W₀,B,W,s,D⟩ := exists_sourceBirkhoffMap_complex_analytic hp hp1
  exact Subset.antisymm (sourceIsospectralSet_subset_actionLevelSet hp hp1 φ)
    (D.actionLevelSet_subset_isospectralSet_all_exponents φ)

end NLS.ZakharovShabat
