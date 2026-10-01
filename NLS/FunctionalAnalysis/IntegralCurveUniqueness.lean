import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Topology.Connected.Clopen

/-! # Uniqueness on connected open time domains

Local Lipschitz uniqueness propagates across a connected time domain:
the equality locus is both closed and open in that domain. The field
only needs to be continuously differentiable at the points of the first
curve, rather than globally Lipschitz on the ambient source space.
-/

noncomputable section
open Set Filter Topology
namespace NLS.FunctionalAnalysis

/-- Actual autonomous integral curves with a common initial value agree
on a connected open time domain if the field is `C¹` along the first
curve. No uniform Lipschitz constant is assumed on the whole domain. -/
theorem eqOn_integralCurves_of_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : E → E) (f g : ℝ → E) (s : Set ℝ)
    (hs : IsOpen s) (hconn : IsPreconnected s)
    (hf : ∀ t ∈ s, HasDerivAt f (V (f t)) t)
    (hg : ∀ t ∈ s, HasDerivAt g (V (g t)) t)
    (hV : ∀ t ∈ s, ContDiffAt ℝ 1 V (f t))
    (t₀ : ℝ) (ht₀ : t₀ ∈ s) (heq : f t₀ = g t₀) : EqOn f g s := by
  have hlocal (t : ℝ) (ht : t ∈ s) (he : f t = g t) : f =ᶠ[𝓝 t] g := by
    obtain ⟨K,U,hU,hLip⟩ := (hV t ht).exists_lipschitzOnWith
    have hfmem : ∀ᶠ u in 𝓝 t, f u ∈ U := (hf t ht).continuousAt.tendsto.eventually hU
    have hUg : U ∈ 𝓝 (g t) := by rwa [← he]
    have hgmem : ∀ᶠ u in 𝓝 t, g u ∈ U := (hg t ht).continuousAt.tendsto.eventually hUg
    apply ODE_solution_unique_of_eventually (v := fun _ => V) (s := fun _ => U)
      (Filter.Eventually.of_forall fun _ => hLip) _ _ he
    · filter_upwards [hs.eventually_mem ht,hfmem] with u hu hfu
      exact ⟨hf u hu,hfu⟩
    · filter_upwards [hs.eventually_mem ht,hgmem] with u hu hgu
      exact ⟨hg u hu,hgu⟩
  let A : Set s := {t | f t.val = g t.val}
  have hfC : Continuous (fun t : s => f t.val) :=
    continuousOn_iff_continuous_domRestrict.mp (HasDerivAt.continuousOn hf)
  have hgC : Continuous (fun t : s => g t.val) :=
    continuousOn_iff_continuous_domRestrict.mp (HasDerivAt.continuousOn hg)
  have hclosed : IsClosed A := isClosed_eq hfC hgC
  have hopen : IsOpen A := by
    rw [isOpen_iff_eventually]
    intro t ht
    exact continuous_subtype_val.continuousAt.tendsto.eventually (hlocal t.val t.property ht)
  let : PreconnectedSpace s := Subtype.preconnectedSpace hconn
  have hall : (univ : Set s) ⊆ A := isPreconnected_univ.subset_isClopen
    ⟨hclosed,hopen⟩ ⟨⟨t₀,ht₀⟩,mem_univ _,heq⟩
  intro t ht
  exact hall (mem_univ (⟨t,ht⟩ : s))

end NLS.FunctionalAnalysis
