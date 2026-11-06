import NLS.SequenceSpaces.LocalScalarActionDescent

/-! # Simultaneous analytic descent through quadratic actions

The source and target neighborhoods are chosen before the function index.
All scalar invariants on the same coordinate domain therefore factor on
one common action neighborhood, including at zero tail actions. Bounds
expressed in the actions descend on precisely the same neighborhood.
-/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [p.HolderTriple p q]

/-- One geometric chart supports an arbitrary family of analytic scalar
invariants. Its open action image and exact recovery are uniform in the index. -/
theorem exists_local_scalar_action_factors {ι : Type*} (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : ι → (Coeff p × Coeff p) → ℂ) (V : Set (Coeff p × Coeff p))
    (hV : IsOpen V) (hf : ∀ i, AnalyticOnNhd ℂ (f i) V)
    (hsign : ∀ i, ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f i (pairSignChange e d z) = f i z)
    (hrot : ∀ i, ∀ z ∈ V, ∀ k, fderiv ℂ (f i) z (actionRotationVectorCLM p k z) = 0)
    (z₀ : Coeff p × Coeff p) (hbase : z₀ ∈ V)
    (hhead : ∀ k ∈ S, z₀.1 k ≠ 0 ∨ z₀.2 k ≠ 0) :
    ∃ Z : Set (Coeff p × Coeff p), ∃ T : Set (Coeff q), ∃ g : ι → Coeff q → ℂ,
      IsOpen Z ∧ z₀ ∈ Z ∧ Z ⊆ V ∧ IsOpen T ∧ quadraticActionsExponent (q := q) '' Z = T ∧
      (∀ i, AnalyticOnNhd ℂ (g i) T) ∧ ∀ i, ∀ z ∈ Z, g i (quadraticActionsExponent z) = f i z := by
  let Q := pairMixedSquare (p := p) (q := q) S
  let G := fun i => tailSquareDescent (q := q) S (f i) V
  have hopen : IsOpen (Q '' V) := isOpenMap_pairMixedSquare hp S V hV
  have hG (i : ι) : AnalyticOnNhd ℂ (G i) (Q '' V) := analyticOnNhd_scalar_tailSquareDescent hp S (f i) V hV (hf i) (hsign i)
  have he (i : ι) (z : Coeff p × Coeff p) (hz : z ∈ V) : G i (Q z) = f i z := tailSquareDescent_apply S (f i) V (hsign i) z hz
  have hsplit (i : ι) := fderiv_actionSplit_eq_zero_of_recovery hp S (f i) (G i) V hV (hf i).differentiableOn (hG i) (he i) (hrot i)
  obtain ⟨L⟩ := exists_tailSumChart S (Q '' V) hopen (Q z₀) ⟨z₀,hbase,rfl⟩
  have hLG (i : ι) := L.analyticOnNhd_factor (G i) (hG i)
  have hLGrot (i : ι) (w : TailSumSpace q S) (hw : w ∈ L.target) (k : S) :
      fderiv ℂ (L.factor (G i)) w (headRotationVector S k w) = 0 :=
    fderiv_tailSumFactor_headRotation_eq_zero (doublingExponent_ne_top hp) S (f i) (G i) V hV hopen
      (hf i).differentiableOn (hG i) (he i) (hsplit i) (hrot i) (Q z₀) L w hw k
  have ha : HeadNonzero S (tailSumCLM S (Q z₀)) := headNonzero_tailSum_mixedSquare S z₀ hhead
  obtain ⟨K⟩ := exists_headActionChart S (tailSumCLM S (Q z₀)) ha L.target L.target_open L.target_base_mem
  let Z := (V ∩ Q ⁻¹' L.source) ∩ (fun z => tailSumCLM S (Q z)) ⁻¹' K.source
  have hQ : Continuous Q := continuousOn_univ.mp (analyticOnNhd_pairMixedSquare S).continuousOn
  have hPQ : Continuous (fun z => tailSumCLM S (Q z)) := (tailSumCLM S).continuous.comp hQ
  have hZ : IsOpen Z := (hV.inter (L.source_open.preimage hQ)).inter (K.source_open.preimage hPQ)
  refine ⟨Z,K.target,(fun i => K.factor (L.factor (G i))),hZ,⟨⟨hbase,L.base_mem⟩,K.base_mem⟩,
    fun z hz => hz.1.1,K.target_open,?_,(fun i => K.analyticOnNhd_factor _ (hLG i)),?_⟩
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
  · intro i z hz
    rw [← headActions_tailSum_mixedSquare S z]
    exact (K.factor_apply L.target_open _ (hLG i).differentiableOn (hLGrot i) _ hz.2).trans
      ((L.factor_apply (doublingExponent_ne_top hp) hopen (G i) (hG i).differentiableOn (hsplit i) (Q z) hz.1.2).trans
        (he i z hz.1.1))


/-- Every action-dependent bound on the source descends to every factor
on the same common action neighborhood. -/
theorem exists_local_scalar_action_factors_with_bounds {ι : Type*} (hp : p ≠ ⊤)
    (S : Finset ℤ) (f : ι → (Coeff p × Coeff p) → ℂ) (V : Set (Coeff p × Coeff p))
    (hV : IsOpen V) (hf : ∀ i, AnalyticOnNhd ℂ (f i) V)
    (hsign : ∀ i, ∀ e d : ℤ → Bool, (∀ n ∈ S, e n = false) → (∀ n ∈ S, d n = false) →
      ∀ z ∈ V, f i (pairSignChange e d z) = f i z)
    (hrot : ∀ i, ∀ z ∈ V, ∀ k, fderiv ℂ (f i) z (actionRotationVectorCLM p k z) = 0)
    (z₀ : Coeff p × Coeff p) (hbase : z₀ ∈ V)
    (hhead : ∀ k ∈ S, z₀.1 k ≠ 0 ∨ z₀.2 k ≠ 0)
    (B : ι → Coeff q → ℝ)
    (hbound : ∀ i, ∀ z ∈ V, ‖f i z‖ ≤ B i (quadraticActionsExponent z)) :
    ∃ Z : Set (Coeff p × Coeff p), ∃ T : Set (Coeff q), ∃ g : ι → Coeff q → ℂ,
      IsOpen Z ∧ z₀ ∈ Z ∧ Z ⊆ V ∧ IsOpen T ∧ quadraticActionsExponent (q := q) '' Z = T ∧
      (∀ i, AnalyticOnNhd ℂ (g i) T) ∧
      (∀ i, ∀ z ∈ Z, g i (quadraticActionsExponent z) = f i z) ∧
      ∀ i, ∀ b ∈ T, ‖g i b‖ ≤ B i b := by
  obtain ⟨Z,T,g,hZ,hbaseZ,hZV,hT,himage,hg,hrec⟩ :=
    exists_local_scalar_action_factors (q := q) hp S f V hV hf hsign hrot z₀ hbase hhead
  refine ⟨Z,T,g,hZ,hbaseZ,hZV,hT,himage,hg,hrec,?_⟩
  intro i b hb
  obtain ⟨z,hz,rfl⟩ := himage.symm ▸ hb
  rw [hrec i z hz]
  exact hbound i z (hZV hz)

end NLS.Coeff
