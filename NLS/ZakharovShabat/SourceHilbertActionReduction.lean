import NLS.SequenceSpaces.RealActionReduction
import NLS.ZakharovShabat.SourceHilbertGlobalInverse
import NLS.ZakharovShabat.SourceBirkhoffFiniteSupport

/-! # Lifting the action-reduction curve to the actual Hilbert source

The proved global inverse lifts the explicit one-mode radial curve. Its
original spectral actions have the exact reduction and conservation laws;
the source curve is smooth before collapse and continuous at collapse.
Its derivative is the inverse Jacobian applied to the radial vector.
Identification with the actual angle Hamiltonian and stronger-exponent
regularity of the source displacement are separate subsequent steps.
-/
noncomputable section
open Set Filter Topology
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- The quadratic coordinate action is the original spectral action. -/
theorem hilbert_pairAction_eq
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) :
    RealCoeff.pairAction (D.hilbertRealHomeomorph φ) k =
      (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re := by
  have h := D.real_map_action_radius φ k
  dsimp only [RealCoeff.pairAction]
  rw [hilbertRealHomeomorph_apply]
  linarith

/-- The radial action-reduction curve in the original source space. -/
def hilbertActionReduction
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) (t : ℝ) : realTypeSourceSubmodule 2 :=
  D.hilbertRealHomeomorph.symm (RealCoeff.actionReduction (D.hilbertRealHomeomorph φ) k t)

@[simp] theorem hilbertRealHomeomorph_actionReduction
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) (t : ℝ) :
    D.hilbertRealHomeomorph (D.hilbertActionReduction φ k t) =
      RealCoeff.actionReduction (D.hilbertRealHomeomorph φ) k t :=
  D.hilbertRealHomeomorph.apply_symm_apply _

@[simp] theorem hilbertActionReduction_zero
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) : D.hilbertActionReduction φ k 0 = φ := by
  simp only [hilbertActionReduction,RealCoeff.actionReduction_zero]
  exact D.hilbertRealHomeomorph.symm_apply_apply φ

/-- The selected original spectral action decreases at exactly unit speed. -/
theorem hilbertActionReduction_action_same
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ)
    (ha : 0 < (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re)
    (t : ℝ) (ht : t ≤ (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re) :
    (sourceRealAction (by simp) (by norm_num) (D.hilbertActionReduction φ k t).val
      (D.hilbertActionReduction φ k t).property k).re =
        (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re-t := by
  rw [← D.hilbert_pairAction_eq,hilbertRealHomeomorph_actionReduction]
  rw [RealCoeff.pairAction_actionReduction_same _ k (by simpa only [D.hilbert_pairAction_eq] using ha)
    t (by simpa only [D.hilbert_pairAction_eq] using ht),D.hilbert_pairAction_eq]

/-- All other original spectral actions are conserved. -/
theorem hilbertActionReduction_action_ne
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k n : ℤ) (hn : n ≠ k) (t : ℝ) :
    (sourceRealAction (by simp) (by norm_num) (D.hilbertActionReduction φ k t).val
      (D.hilbertActionReduction φ k t).property n).re =
        (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re := by
  rw [← D.hilbert_pairAction_eq,hilbertRealHomeomorph_actionReduction,
    RealCoeff.pairAction_actionReduction_ne _ k n hn t,D.hilbert_pairAction_eq]

/-- The full source curve is continuous even at the collapsed endpoint. -/
theorem continuous_hilbertActionReduction
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) : Continuous (D.hilbertActionReduction φ k) :=
  D.hilbertRealHomeomorph.symm.continuous.comp (RealCoeff.continuous_actionReduction _ k)

/-- Smoothness on the complete interval before collapse, including negative times. -/
theorem contDiffAt_hilbertActionReduction
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ)
    (ha : 0 < (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re)
    {t : ℝ} (ht : t < (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re) :
    ContDiffAt ℝ ⊤ (D.hilbertActionReduction φ k) t :=
  (D.hilbertRealHomeomorph_symm_analytic _ (mem_univ _)).contDiffAt.comp t
    (RealCoeff.contDiffAt_actionReduction _ k
      (by simpa only [D.hilbert_pairAction_eq] using ha)
      (by simpa only [D.hilbert_pairAction_eq] using ht))

/-- The derivative of the global inverse is the inverse of the actual Jacobian. -/
theorem hilbertRealHomeomorph_symm_hasStrictFDerivAt
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (y : RealCoeff 2 × RealCoeff 2) :
    HasStrictFDerivAt D.hilbertRealHomeomorph.symm
      (D.realJacobianEquivAll (D.hilbertRealHomeomorph.symm y)).symm.toContinuousLinearMap y := by
  let φ := D.hilbertRealHomeomorph.symm y
  have hφ : sourceRealBirkhoffMap (by simp) (by norm_num) s φ = y :=
    D.hilbertRealHomeomorph.apply_symm_apply y
  obtain ⟨g,_,_,_,hr,hd⟩ := D.proposition17_1 φ
  rw [hφ] at hr hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [hr] with z hz
  apply D.hilbert_real_map_bijective.1
  exact hz.trans (D.hilbertRealHomeomorph.apply_symm_apply z).symm

/-- The radial vector pulled back by the actual source Jacobian. -/
def hilbertActionReductionVector
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) : realTypeSourceSubmodule 2 :=
  (D.realJacobianEquivAll φ).symm (RealCoeff.actionReductionVector (D.hilbertRealHomeomorph φ) k)

/-- The lifted curve solves the pullback radial differential equation. -/
theorem hasDerivAt_hilbertActionReduction
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ)
    (ha : 0 < (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re)
    {t : ℝ} (ht : t < (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re) :
    HasDerivAt (D.hilbertActionReduction φ k)
      (D.hilbertActionReductionVector (D.hilbertActionReduction φ k t) k) t := by
  have hd := (D.hilbertRealHomeomorph_symm_hasStrictFDerivAt
    (RealCoeff.actionReduction (D.hilbertRealHomeomorph φ) k t)).hasFDerivAt.comp_hasDerivAt t
      (RealCoeff.hasDerivAt_actionReduction_vector _ k
        (by simpa only [D.hilbert_pairAction_eq] using ha)
        (by simpa only [D.hilbert_pairAction_eq] using ht))
  simpa only [hilbertActionReductionVector,hilbertRealHomeomorph_actionReduction] using! hd

/-- The selected action tends to zero from below its collapse time. -/
theorem tendsto_action_hilbertActionReduction
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ)
    (ha : 0 < (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re) :
    Tendsto (fun t : ℝ => (sourceRealAction (by simp) (by norm_num)
      (D.hilbertActionReduction φ k t).val (D.hilbertActionReduction φ k t).property k).re)
      (𝓝[<] (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re) (𝓝 0) := by
  let a := (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re
  have ht : Tendsto (fun t : ℝ => a-t) (𝓝[<] a) (𝓝 (a-a)) :=
    tendsto_const_nhds.sub (tendsto_id.mono_left nhdsWithin_le_nhds)
  simp only [sub_self] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (D.hilbertActionReduction_action_same φ k ha t ht.le).symm

/-- There is a source-norm limit at the collapse time. -/
theorem tendsto_hilbertActionReduction_at_collapse
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) :
    let a := (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re
    Tendsto (D.hilbertActionReduction φ k) (𝓝[<] a) (𝓝 (D.hilbertActionReduction φ k a)) :=
  (D.continuous_hilbertActionReduction φ k).continuousAt.tendsto.mono_left nhdsWithin_le_nhds

/-- The limit source has its selected periodic gap closed. -/
theorem hilbertActionReduction_gap_zero_at_collapse
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ)
    (ha : 0 < (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re) :
    let a := (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re
    sourcePeriodicGapDisplacement (by simp) (by norm_num) (D.hilbertActionReduction φ k a).val k = 0 := by
  dsimp only
  let a := (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re
  let ψ := D.hilbertActionReduction φ k a
  have hz := sourceRealAction_nonneg_and_eq_zero_iff_gap_zero (by simp) (by norm_num) ψ.val ψ.property k
  apply hz.2.2.mp
  apply Complex.ext
  · change (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property k).re = 0
    have h := D.hilbertActionReduction_action_same φ k ha a (le_refl a)
    simpa only [a,sub_self] using h
  · exact hz.2.1

/-- Any positive selected action can be made arbitrarily small at a
nonnegative time before collapse, while all other actions are preserved. -/
theorem exists_hilbertActionReduction_small_action
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ)
    (ha : 0 < (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ t : ℝ, 0 ≤ t ∧ t < (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re ∧
      let ψ := D.hilbertActionReduction φ k t
      0 < (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property k).re ∧
      (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property k).re < ε ∧
      ∀ n : ℤ, n ≠ k → (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n).re =
        (sourceRealAction (by simp) (by norm_num) φ.val φ.property n).re := by
  let a := (sourceRealAction (by simp) (by norm_num) φ.val φ.property k).re
  let δ := min a ε / 2
  have hδ : 0 < δ := half_pos (lt_min ha hε)
  have hδa : δ ≤ a := by dsimp [δ]; have := min_le_left a ε; linarith
  have hδε : δ < ε := by dsimp [δ]; have := min_le_right a ε; linarith
  refine ⟨a-δ,sub_nonneg.mpr hδa,by change a-δ < a; linarith,?_⟩
  dsimp only
  have he := D.hilbertActionReduction_action_same φ k ha (a-δ) (by change a-δ ≤ a; linarith)
  have he' : (sourceRealAction (by simp) (by norm_num) (D.hilbertActionReduction φ k (a-δ)).val
      (D.hilbertActionReduction φ k (a-δ)).property k).re = δ := by
    change _ = a-(a-δ) at he
    linarith
  refine ⟨by rw [he']; exact hδ,by rw [he']; exact hδε,?_⟩
  intro n hn
  exact D.hilbertActionReduction_action_ne φ k n hn (a-δ)

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
