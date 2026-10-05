import NLS.SequenceSpaces.ScalarTailSquareDescent
import NLS.SequenceSpaces.HeadRotationDescent
import NLS.SequenceSpaces.LocalHeadActionDescent

/-! # Local scalar analytic factors through all quadratic actions

Tail sign symmetry and rotation stationarity remove the choice of roots
and the split between each coordinate pair. Zero tail actions are allowed.
-/
noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- An analytic scalar invariant has a local analytic action factor with
exact recovery throughout an open neighborhood of the original point. -/
theorem exists_local_scalar_action_factor (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : (Coeff p × Coeff p) → ℂ) (V : Set (Coeff p × Coeff p))
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V)
    (hsign : ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f (pairSignChange e d z) = f z)
    (hrot : ∀ z ∈ V, ∀ k, fderiv ℂ f z (actionRotationVectorCLM p k z) = 0)
    (z₀ : Coeff p × Coeff p) (hbase : z₀ ∈ V)
    (hhead : ∀ k ∈ S, z₀.1 k ≠ 0 ∨ z₀.2 k ≠ 0) :
    ∃ Z : Set (Coeff p × Coeff p), ∃ T : Set (Coeff q), ∃ g : Coeff q → ℂ,
      IsOpen Z ∧ z₀ ∈ Z ∧ Z ⊆ V ∧ IsOpen T ∧ quadraticActionsExponent (q := q) '' Z = T ∧
      AnalyticOnNhd ℂ g T ∧ ∀ z ∈ Z, g (quadraticActionsExponent z) = f z := by
  let Q := pairMixedSquare (p := p) (q := q) S
  let G := tailSquareDescent (q := q) S f V
  have hopen : IsOpen (Q '' V) := isOpenMap_pairMixedSquare hp S V hV
  have hG : AnalyticOnNhd ℂ G (Q '' V) := analyticOnNhd_scalar_tailSquareDescent hp S f V hV hf hsign
  have he (z : Coeff p × Coeff p) (hz : z ∈ V) : G (Q z) = f z := tailSquareDescent_apply S f V hsign z hz
  have hsplit := fderiv_actionSplit_eq_zero_of_recovery hp S f G V hV hf.differentiableOn hG he hrot
  obtain ⟨L⟩ := exists_tailSumChart S (Q '' V) hopen (Q z₀) ⟨z₀,hbase,rfl⟩
  have hLG := L.analyticOnNhd_factor G hG
  have hLGrot (w : TailSumSpace q S) (hw : w ∈ L.target) (k : S) :
      fderiv ℂ (L.factor G) w (headRotationVector S k w) = 0 :=
    fderiv_tailSumFactor_headRotation_eq_zero (doublingExponent_ne_top hp) S f G V hV hopen
      hf.differentiableOn hG he hsplit hrot (Q z₀) L w hw k
  have ha : HeadNonzero S (tailSumCLM S (Q z₀)) := headNonzero_tailSum_mixedSquare S z₀ hhead
  obtain ⟨K⟩ := exists_headActionChart S (tailSumCLM S (Q z₀)) ha L.target L.target_open L.target_base_mem
  let Z := (V ∩ Q ⁻¹' L.source) ∩ (fun z => tailSumCLM S (Q z)) ⁻¹' K.source
  have hQ : Continuous Q := continuousOn_univ.mp (analyticOnNhd_pairMixedSquare S).continuousOn
  have hPQ : Continuous (fun z => tailSumCLM S (Q z)) := (tailSumCLM S).continuous.comp hQ
  have hZ : IsOpen Z := (hV.inter (L.source_open.preimage hQ)).inter (K.source_open.preimage hPQ)
  refine ⟨Z,K.target,K.factor (L.factor G),hZ,⟨⟨hbase,L.base_mem⟩,K.base_mem⟩,
    fun z hz => hz.1.1,K.target_open,?_,K.analyticOnNhd_factor _ hLG,?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      simpa only [Q,headActions_tailSum_mixedSquare] using K.map_mem (tailSumCLM S (Q z)) hz.2
    · intro b hb
      let w := headActionSection S (tailSumCLM S (Q z₀)) b
      have hw : w ∈ K.source := K.section_mem b hb
      obtain ⟨z,hz,hQz⟩ := L.source_subset (L.section_mem w (K.source_subset hw))
      change Q z = tailSumSection S (Q z₀) w at hQz
      have hPz : tailSumCLM S (Q z) = w := by rw [hQz,tailSum_section]
      refine ⟨z,⟨⟨hz,?_⟩,?_⟩,?_⟩
      · change Q z ∈ L.source
        rw [hQz]
        exact L.section_mem w (K.source_subset hw)
      · change tailSumCLM S (Q z) ∈ K.source
        simpa only [hPz] using hw
      · rw [← headActions_tailSum_mixedSquare S z,hPz]
        exact headActions_section S _ K.head_nonzero b
  · intro z hz
    rw [← headActions_tailSum_mixedSquare S z]
    exact (K.factor_apply L.target_open _ hLG.differentiableOn hLGrot _ hz.2).trans
      ((L.factor_apply (doublingExponent_ne_top hp) hopen G hG.differentiableOn hsplit (Q z) hz.1.2).trans
        (he z hz.1.1))

end NLS.Coeff
