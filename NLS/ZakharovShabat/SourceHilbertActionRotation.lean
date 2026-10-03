import NLS.SequenceSpaces.RealActionRotation
import NLS.ZakharovShabat.SourceBirkhoffActionHamiltonian
import NLS.ZakharovShabat.SourceHilbertActionReduction
import NLS.ZakharovShabat.SourceIsospectralDirection
import NLS.ZakharovShabat.SourceIsospectralSet

/-! # Complete isospectral Hilbert action flows

The global Birkhoff inverse lifts every one-mode coordinate rotation.
Its derivative is the original action Hamiltonian, by the exact inverse
Jacobian and canonical Poisson relations. The discriminant is constant
along the entire curve, so every time and every finite composition
preserves the original periodic spectrum and algebraic multiplicities.
-/
noncomputable section
open Set Filter Topology NLS.Poisson
namespace NLS.ZakharovShabat.SourceBirkhoffMapComplexData
variable {W₀ B W : Set (CoeffPair 2)} {s : (k : ℤ) → CoeffPair 2 → DeletedCoeff 2 k}

/-- The complete action flow lifted to the original Hilbert source. -/
def hilbertActionRotation
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) (t : ℝ) : realTypeSourceSubmodule 2 :=
  D.hilbertRealHomeomorph.symm (RealCoeff.actionRotation (D.hilbertRealHomeomorph φ) k t)

@[simp] theorem hilbertRealHomeomorph_actionRotation
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) (t : ℝ) :
    D.hilbertRealHomeomorph (D.hilbertActionRotation φ k t) =
      RealCoeff.actionRotation (D.hilbertRealHomeomorph φ) k t :=
  D.hilbertRealHomeomorph.apply_symm_apply _

@[simp] theorem hilbertActionRotation_zero
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) : D.hilbertActionRotation φ k 0 = φ := by
  simp only [hilbertActionRotation,RealCoeff.actionRotation_zero]
  exact D.hilbertRealHomeomorph.symm_apply_apply φ

/-- The source flow has the additive time law, including negative times. -/
theorem hilbertActionRotation_add
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) (t u : ℝ) :
    D.hilbertActionRotation (D.hilbertActionRotation φ k t) k u =
      D.hilbertActionRotation φ k (t+u) := by
  apply D.hilbertRealHomeomorph.injective
  simp only [hilbertRealHomeomorph_actionRotation,RealCoeff.actionRotation_add]

/-- The complex Jacobian sends the original action Hamiltonian to a rotation. -/
theorem hilbert_jacobian_actionHamiltonian
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (k : ℤ) (φ : realTypeSourceSubmodule 2) :
    sourceBirkhoffJacobian (by simp) (by norm_num) s φ.val
      (sourceHamiltonianVector (le_refl 2) (sourceComplexAction (by simp) (by norm_num) k) φ.val) =
    ((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2))
      (RealCoeff.actionRotationVector (D.hilbertRealHomeomorph φ) k) := by
  let v := sourceHamiltonianVector (le_refl 2) (sourceComplexAction (by simp) (by norm_num) k) φ.val
  have hrow (n : ℤ) := D.jacobian_coordinates φ.val (D.real_subset φ.property) v n
  have hd (n : ℤ) := D.fderiv_coordinates n φ.val (D.real_subset φ.property)
  have hv (n : ℤ) := D.map_coordinates_actionHamiltonian (le_refl 2) k n φ
  have hval : sourceBirkhoffMap (by simp) (by norm_num) s φ.val =
      ((RealCoeff.complexCLM 2).prodMap (RealCoeff.complexCLM 2)) (D.hilbertRealHomeomorph φ) :=
    (D.real_map_complex_inclusion φ).symm
  apply Prod.ext <;> ext n
  · rw [(hrow n).1,← (hd n).1]
    refine (hv n).1.trans ?_
    rw [hval]
    change -((D.hilbertRealHomeomorph φ).2 k : ℂ)*(if n = k then 1 else 0) =
      (-(lp.single (E := fun _ : ℤ => ℝ) 2 k ((D.hilbertRealHomeomorph φ).2 k)) n : ℝ)
    by_cases hn : n = k <;> simp [lp.single_apply,hn]
  · rw [(hrow n).2,← (hd n).2]
    refine (hv n).2.trans ?_
    rw [hval]
    change ((D.hilbertRealHomeomorph φ).1 k : ℂ)*(if n = k then 1 else 0) =
      ((lp.single (E := fun _ : ℤ => ℝ) 2 k ((D.hilbertRealHomeomorph φ).1 k)) n : ℝ)
    by_cases hn : n = k <;> simp [lp.single_apply,hn]

/-- The rotation velocity pulled back to the real source. -/
def hilbertActionRotationVector
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) : realTypeSourceSubmodule 2 :=
  (D.realJacobianEquivAll φ).symm (RealCoeff.actionRotationVector (D.hilbertRealHomeomorph φ) k)

/-- The pulled-back velocity is exactly the original action Hamiltonian. -/
theorem hilbertActionRotationVector_eq_actionHamiltonian
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (k : ℤ) (φ : realTypeSourceSubmodule 2) :
    (D.hilbertActionRotationVector φ k).val =
      sourceHamiltonianVector (le_refl 2) (sourceComplexAction (by simp) (by norm_num) k) φ.val := by
  apply (D.jacobian_bijective_all_exponents φ).1
  rw [D.hilbert_jacobian_actionHamiltonian k φ,
    ← D.real_jacobian_complex_inclusion φ (D.hilbertActionRotationVector φ k)]
  congr 1
  exact (D.realJacobianEquivAll φ).apply_symm_apply _

/-- The derivative exists in the full original source norm at every time. -/
theorem hasDerivAt_hilbertActionRotation
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) (t : ℝ) :
    HasDerivAt (D.hilbertActionRotation φ k)
      (D.hilbertActionRotationVector (D.hilbertActionRotation φ k t) k) t := by
  have hd := (D.hilbertRealHomeomorph_symm_hasStrictFDerivAt
    (RealCoeff.actionRotation (D.hilbertRealHomeomorph φ) k t)).hasFDerivAt.comp_hasDerivAt t
      (RealCoeff.hasDerivAt_actionRotation _ k t)
  simpa only [hilbertActionRotationVector,hilbertRealHomeomorph_actionRotation] using! hd

/-- The lifted curve solves the actual action Hamiltonian equation globally. -/
theorem hasDerivAt_hilbertActionRotation_actionHamiltonian
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (D.hilbertActionRotation φ k t).val)
      (sourceHamiltonianVector (le_refl 2) (sourceComplexAction (by simp) (by norm_num) k)
        (D.hilbertActionRotation φ k t).val) t := by
  have hd := (realTypeSourceSubmodule 2).subtypeL.hasFDerivAt.comp_hasDerivAt t
    (D.hasDerivAt_hilbertActionRotation φ k t)
  change HasDerivAt (fun t : ℝ => (D.hilbertActionRotation φ k t).val)
    (D.hilbertActionRotationVector (D.hilbertActionRotation φ k t) k).val t at hd
  rw [D.hilbertActionRotationVector_eq_actionHamiltonian] at hd
  exact hd

/-- The actual normalized discriminant is constant along every complete action flow. -/
theorem discriminant_hilbertActionRotation
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) (t : ℝ) :
    canonicalDiscriminant (by simp) (periodOnePotential (D.hilbertActionRotation φ k t).val) =
      canonicalDiscriminant (by simp) (periodOnePotential φ.val) := by
  funext z
  have hd (u : ℝ) : HasDerivAt (fun u : ℝ => canonicalDiscriminant (by simp)
      (periodOnePotential (D.hilbertActionRotation φ k u).val) z) 0 u := by
    have hf := (analyticOnNhd_sourceDiscriminant_section (p := 2) (by simp) (by norm_num) z
      (D.hilbertActionRotation φ k u).val (mem_univ _)).differentiableAt
    have hc := (hf.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt u
      (D.hasDerivAt_hilbertActionRotation_actionHamiltonian φ k u)
    have hz := sourceHamiltonianVector_action_isospectral (by simp) (by norm_num) (le_refl 2)
      (D.hilbertActionRotation φ k u).val (D.hilbertActionRotation φ k u).property k z
    convert! hc using 1
    exact hz.symm
  have he := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) t 0
  simpa only [hilbertActionRotation_zero] using he

/-- Every time of the action flow preserves the original spectrum and multiplicities. -/
theorem hilbertActionRotation_mem_isospectralSet
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (k : ℤ) (t : ℝ) :
    D.hilbertActionRotation φ k t ∈ sourceIsospectralSet (by simp) φ :=
  (mem_sourceIsospectralSet_iff_discriminant_eq (by simp) (by norm_num) φ _).mpr
    (D.discriminant_hilbertActionRotation φ k t)

/-- Finite action rotations, in the given list order. -/
def hilbertActionRotationSequence
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (moves : List (ℤ × ℝ)) : realTypeSourceSubmodule 2 :=
  moves.foldl (fun ψ move => D.hilbertActionRotation ψ move.1 move.2) φ

/-- Finite source rotations give exactly the corresponding coordinate rotations. -/
theorem hilbertRealHomeomorph_actionRotationSequence
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (moves : List (ℤ × ℝ)) :
    D.hilbertRealHomeomorph (D.hilbertActionRotationSequence φ moves) =
      moves.foldl (fun z move => RealCoeff.actionRotation z move.1 move.2) (D.hilbertRealHomeomorph φ) := by
  induction moves generalizing φ with
  | nil => rfl
  | cons move moves ih =>
    simpa only [hilbertActionRotationSequence,List.foldl_cons,hilbertRealHomeomorph_actionRotation]
      using ih (D.hilbertActionRotation φ move.1 move.2)

/-- No time or open-gap restrictions are needed for finite isospectral transport. -/
theorem hilbertActionRotationSequence_mem_isospectralSet
    (D : SourceBirkhoffMapComplexData (by simp) (by norm_num) W₀ B W s)
    (φ : realTypeSourceSubmodule 2) (moves : List (ℤ × ℝ)) :
    D.hilbertActionRotationSequence φ moves ∈ sourceIsospectralSet (by simp) φ := by
  apply (mem_sourceIsospectralSet_iff_discriminant_eq (by simp) (by norm_num) φ _).mpr
  induction moves generalizing φ with
  | nil => rfl
  | cons move moves ih =>
    exact (ih (D.hilbertActionRotation φ move.1 move.2)).trans
      (D.discriminant_hilbertActionRotation φ move.1 move.2)

end NLS.ZakharovShabat.SourceBirkhoffMapComplexData
