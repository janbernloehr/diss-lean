import NLS.SequenceSpaces.ScalarActionDescentFromRealGerms

/-! Simultaneous scalar analytic action descent on ONE common neighborhood.
The tail-sum and head charts depend only on the original domain and base,
so they can be chosen before an arbitrary family of scalar invariants. -/
noncomputable section
set_option autoImplicit false
open Set Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p q : ℝ≥0∞} [Fact (1≤p)] [Fact (1≤q)] [p.HolderTriple p q]
variable {ι : Type*}

/-- ONE pair of action/source neighborhoods works before EVERY scalar
component. Analyticity here is explicitly componentwise; no target sequence
norm or sequence-valued analyticity is inferred. -/
theorem exists_local_scalar_action_family (hp : p≠⊤)
    (S : Finset ℤ) (f : ι → (Coeff p × Coeff p) → ℂ) (V : Set (Coeff p × Coeff p))
    (hV : IsOpen V) (hf : ∀ i, AnalyticOnNhd ℂ (f i) V)
    (hsign : ∀ i, ∀ e d : ℤ → Bool, (∀ n∈S, e n=false) → (∀ n∈S, d n=false) →
      ∀ z∈V, f i (pairSignChange e d z)=f i z)
    (hrot : ∀ i, ∀ z∈V, ∀ k, fderiv ℂ (f i) z (actionRotationVectorCLM p k z)=0)
    (z₀ : Coeff p × Coeff p) (hbase : z₀∈V)
    (hhead : ∀ k∈S, z₀.1 k≠0 ∨ z₀.2 k≠0) :
    ∃ Z : Set (Coeff p × Coeff p), ∃ T : Set (Coeff q), ∃ g : ι → Coeff q → ℂ,
      IsOpen Z ∧ z₀∈Z ∧ Z⊆V ∧ IsOpen T ∧ quadraticActionsExponent (q := q) '' Z=T ∧
      (∀ i, AnalyticOnNhd ℂ (g i) T) ∧ ∀ i, ∀ z∈Z, g i (quadraticActionsExponent z)=f i z := by
  let Q := pairMixedSquare (p := p) (q := q) S
  let G := fun i => tailSquareDescent (q := q) S (f i) V
  have hopen : IsOpen (Q '' V) := isOpenMap_pairMixedSquare hp S V hV
  have hG (i : ι) : AnalyticOnNhd ℂ (G i) (Q '' V) :=
    analyticOnNhd_scalar_tailSquareDescent hp S (f i) V hV (hf i) (hsign i)
  have he (i : ι) (z : Coeff p × Coeff p) (hz : z∈V) : G i (Q z)=f i z :=
    tailSquareDescent_apply S (f i) V (hsign i) z hz
  have hsplit (i : ι) := fderiv_actionSplit_eq_zero_of_recovery hp S (f i) (G i) V hV
    (hf i).differentiableOn (hG i) (he i) (hrot i)
  obtain ⟨L⟩ := exists_tailSumChart S (Q '' V) hopen (Q z₀) ⟨z₀,hbase,rfl⟩
  have hLG (i : ι) := L.analyticOnNhd_factor (G i) (hG i)
  have hLGrot (i : ι) (w : TailSumSpace q S) (hw : w∈L.target) (k : S) :
      fderiv ℂ (L.factor (G i)) w (headRotationVector S k w)=0 :=
    fderiv_tailSumFactor_headRotation_eq_zero (doublingExponent_ne_top hp) S (f i) (G i) V hV hopen
      (hf i).differentiableOn (hG i) (he i) (hsplit i) (hrot i) (Q z₀) L w hw k
  have ha : HeadNonzero S (tailSumCLM S (Q z₀)) := headNonzero_tailSum_mixedSquare S z₀ hhead
  obtain ⟨K⟩ := exists_headActionChart S (tailSumCLM S (Q z₀)) ha L.target L.target_open L.target_base_mem
  let Z := (V ∩ Q ⁻¹' L.source) ∩ (fun z => tailSumCLM S (Q z)) ⁻¹' K.source
  have hQ : Continuous Q := continuousOn_univ.mp (analyticOnNhd_pairMixedSquare S).continuousOn
  have hPQ : Continuous (fun z => tailSumCLM S (Q z)) := (tailSumCLM S).continuous.comp hQ
  have hZ : IsOpen Z := (hV.inter (L.source_open.preimage hQ)).inter (K.source_open.preimage hPQ)
  refine ⟨Z,K.target,(fun i => K.factor (L.factor (G i))),hZ,⟨⟨hbase,L.base_mem⟩,K.base_mem⟩,
    (fun z hz => hz.1.1),K.target_open,?_,(fun i => K.analyticOnNhd_factor _ (hLG i)),?_⟩
  · apply Subset.antisymm
    · rintro _ ⟨z,hz,rfl⟩
      simpa only [Q,headActions_tailSum_mixedSquare] using K.map_mem (tailSumCLM S (Q z)) hz.2
    · intro b hb
      let w := headActionSection S (tailSumCLM S (Q z₀)) b
      have hw : w∈K.source := K.section_mem b hb
      obtain ⟨z,hz,hQz⟩ := L.source_subset (L.section_mem w (K.source_subset hw))
      change Q z=tailSumSection S (Q z₀) w at hQz
      have hPz : tailSumCLM S (Q z)=w := by rw [hQz,tailSum_section]
      refine ⟨z,⟨⟨hz,?_⟩,?_⟩,?_⟩
      · change Q z∈L.source
        rw [hQz]
        exact L.section_mem w (K.source_subset hw)
      · change tailSumCLM S (Q z)∈K.source
        simpa only [hPz] using hw
      · rw [←headActions_tailSum_mixedSquare S z,hPz]
        exact headActions_section S _ K.head_nonzero b
  · intro i z hz
    rw [←headActions_tailSum_mixedSquare S z]
    exact (K.factor_apply L.target_open _ (hLG i).differentiableOn (hLGrot i) _ hz.2).trans
      ((L.factor_apply (doublingExponent_ne_top hp) hopen (G i) (hG i).differentiableOn (hsplit i) (Q z) hz.1.2).trans
        (he i z hz.1.1))

/-- A family of genuine analytic real action invariants has common complex
action neighborhoods, chosen before the component index, also at closed actions. -/
theorem exists_local_scalar_action_family_of_real_invariance (hp : p≠⊤)
    (f : ι → (Coeff p × Coeff p) → ℂ) (U : Set (Coeff p × Coeff p))
    (hU : IsOpen U) (hf : ∀ i, AnalyticOnNhd ℂ (f i) U)
    (hinv : ∀ i, ∀ z∈U, ∀ w∈U, z∈realPairLocus p → w∈realPairLocus p →
      (∀ n, w.1 n^2+w.2 n^2=z.1 n^2+z.2 n^2) → f i w=f i z)
    (z₀ : Coeff p × Coeff p) (hz₀ : z₀∈U) (hr₀ : z₀∈realPairLocus p) :
    ∃ Z : Set (Coeff p × Coeff p), ∃ T : Set (Coeff q), ∃ g : ι → Coeff q → ℂ,
      IsOpen Z ∧ z₀∈Z ∧ Z⊆U ∧ IsOpen T ∧ quadraticActionsExponent (q := q) '' Z=T ∧
      (∀ i, AnalyticOnNhd ℂ (g i) T) ∧ ∀ i, ∀ z∈Z, g i (quadraticActionsExponent z)=f i z := by
  obtain ⟨S,R,hR,hbase,hball,hhead⟩ := exists_nonzeroFiniteCenter_ball hp U hU z₀ hz₀
  let c := truncatePair S z₀
  have hcr : c∈realPairLocus p := truncatePair_mem_realPairLocus S z₀ hr₀
  have hI (i : ι) : ∀ z∈ball c R, ∀ w∈ball c R, z∈realPairLocus p → w∈realPairLocus p →
      (∀ n, w.1 n^2+w.2 n^2=z.1 n^2+z.2 n^2) → f i w=f i z :=
    fun z hz w hw => hinv i z (hball hz) w (hball hw)
  have hsign (i : ι) : ∀ e d : ℤ → Bool, (∀ n∈S, e n=false) → (∀ n∈S, d n=false) →
      ∀ z∈ball c R, f i (pairSignChange e d z)=f i z := by
    intro e d he hd z hz
    exact eqOn_pairSignChange_of_real_action_invariance (f i) c R hR hcr ((hf i).mono hball) (hI i)
      e d (pairSignChange_truncatePair S z₀ e d he hd) hz
  have hrot (i : ι) : ∀ z∈ball c R, ∀ k, fderiv ℂ (f i) z (actionRotationVectorCLM p k z)=0 := by
    intro z hz k
    exact fderiv_actionRotationVector_eq_zero_of_real_action_invariance (f i) _ isOpen_ball
      (convex_ball c R) c (mem_ball_self hR) hcr ((hf i).mono hball) (hI i) z hz k
  obtain ⟨Z,T,g,hZ,hz,hsub,hT,himage,hg,hrec⟩ := exists_local_scalar_action_family
    (q := q) hp S f (ball c R) isOpen_ball (fun i => (hf i).mono hball) hsign hrot z₀ hbase hhead
  exact ⟨Z,T,g,hZ,hz,hsub.trans hball,hT,himage,hg,hrec⟩

end NLS.Coeff
