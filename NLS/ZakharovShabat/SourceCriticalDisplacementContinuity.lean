import NLS.SequenceSpaces.UniformTailContinuity
import NLS.SequenceSpaces.ExponentEmbedding
import NLS.ZakharovShabat.SourceCriticalGapQuotientUniform
import NLS.ZakharovShabat.SourcePeriodicMidpointAsymptotics
import NLS.ZakharovShabat.SourcePeriodicGapTails
import NLS.ZakharovShabat.CanonicalCriticalContinuity

/-!
# Norm continuity of the critical-root displacement sequence

The deleted spectral factor is a joint analytic function of the
critical-root displacement sequence and the source. To use that fact
when a gap collapses, the entire critical displacement must vary
continuously in `ℓp`, rather than only coordinatewise. The squared-gap
identity and locally uniform periodic-gap tails provide this upgrade.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source critical-root displacements, as one `ℓp` sequence. -/
abbrev sourceCriticalDisplacement
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) : Coeff p :=
  canonicalCriticalDisplacement hp hp1
    (periodOnePotential ψ) (periodOnePotential_mem ψ)

/-- The squared-gap offset sequence in Lemma 10.10, represented by
two bounded multipliers acting on the periodic-gap sequence. -/
def sourceCriticalGapSquareOffset
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) : Coeff p :=
  Coeff.multiplier
    (Coeff.exponentInclusion (le_top : p ≤ ⊤)
      (sourceCriticalGapQuotient hp hp1 ψ))
    (Coeff.multiplier
      (Coeff.exponentInclusion (le_top : p ≤ ⊤)
        (sourcePeriodicGapDisplacement hp hp1 ψ))
      (sourcePeriodicGapDisplacement hp hp1 ψ))

@[simp] theorem sourceCriticalGapSquareOffset_apply
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (n : ℤ) :
    sourceCriticalGapSquareOffset hp hp1 ψ n =
      (sourcePeriodicGapDisplacement hp hp1 ψ n)^2 *
        sourceCriticalGapQuotient hp hp1 ψ n := by
  simp only [sourceCriticalGapSquareOffset, Coeff.multiplier_apply,
    Coeff.exponentInclusion_apply]
  ring

/-- Removing the same finite set from the squared-gap offset costs at
most the gap tail times the full gap and critical-quotient norms. -/
theorem norm_sourceCriticalGapSquareOffset_sub_truncate_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (s : Finset ℤ) :
    ‖sourceCriticalGapSquareOffset hp hp1 ψ -
      Coeff.truncate s (sourceCriticalGapSquareOffset hp hp1 ψ)‖ ≤
      ‖sourceCriticalGapQuotient hp hp1 ψ‖ *
        ‖sourcePeriodicGapDisplacement hp hp1 ψ‖ *
          ‖sourcePeriodicGapDisplacement hp hp1 ψ -
            Coeff.truncate s (sourcePeriodicGapDisplacement hp hp1 ψ)‖ := by
  let B := sourceCriticalGapQuotient hp hp1 ψ
  let γ := sourcePeriodicGapDisplacement hp hp1 ψ
  let Btop := Coeff.exponentInclusion (le_top : p ≤ ⊤) B
  let γtop := Coeff.exponentInclusion (le_top : p ≤ ⊤) γ
  have heq : sourceCriticalGapSquareOffset hp hp1 ψ -
      Coeff.truncate s (sourceCriticalGapSquareOffset hp hp1 ψ) =
      Coeff.multiplier Btop (Coeff.multiplier γtop (γ-Coeff.truncate s γ)) := by
    ext n
    by_cases hn : n ∈ s
    · simp [Btop,γtop,B,γ,hn]
    · simp [Btop,γtop,B,γ,hn,sourceCriticalGapSquareOffset_apply]
      ring
  rw [heq]
  calc
    ‖Coeff.multiplier Btop (Coeff.multiplier γtop (γ-Coeff.truncate s γ))‖ ≤
        ‖Btop‖ * ‖Coeff.multiplier γtop (γ-Coeff.truncate s γ)‖ :=
      Coeff.norm_multiplier_le _ _
    _ ≤ ‖Btop‖ * (‖γtop‖ * ‖γ-Coeff.truncate s γ‖) :=
      mul_le_mul_of_nonneg_left (Coeff.norm_multiplier_le _ _) (norm_nonneg _)
    _ ≤ ‖B‖ * (‖γ‖ * ‖γ-Coeff.truncate s γ‖) := by
      have hB := Coeff.norm_exponentInclusion_le le_top B
      have hγ := Coeff.norm_exponentInclusion_le le_top γ
      gcongr
    _ = ‖B‖ * ‖γ‖ * ‖γ-Coeff.truncate s γ‖ := by ring

/-- On the common almost-real domain, the critical displacement is
the periodic midpoint displacement plus its squared-gap offset. -/
theorem exists_global_sourceCriticalDisplacement_eq_midpoint_add_offset
    (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧
      realTypeSourceLocus p ⊆ W ∧
      ∀ ψ ∈ W,
        sourceCriticalDisplacement hp hp1 ψ =
          sourcePeriodicMidpointDisplacement hp hp1 ψ +
            sourceCriticalGapSquareOffset hp hp1 ψ := by
  obtain ⟨W,hWopen,_,hreal,hexact⟩ :=
    exists_global_sourceCriticalPoints_midpoint_gap_sq_exact hp hp1
  refine ⟨W,hWopen,hreal,?_⟩
  intro ψ hψ
  ext n
  have h := (hexact ψ hψ n).2
  simp only [lp.coeFn_add, Pi.add_apply, sourceCriticalDisplacement,
    canonicalCriticalDisplacement_apply,
    sourcePeriodicMidpointDisplacement_apply,
    sourceCriticalGapSquareOffset_apply, sourceCriticalGapQuotient_apply]
  linear_combination h

/-- The full `ℓp` critical displacement has locally uniformly small
finite tails near every real-type source. -/
theorem exists_local_sourceCriticalDisplacement_uniform_tails
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset ℤ, ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∀ ψ ∈ V,
        ‖sourceCriticalDisplacement hp hp1 ψ -
          Coeff.truncate s (sourceCriticalDisplacement hp hp1 ψ)‖ ≤ ε := by
  obtain ⟨VB,hVBopen,hφVB,B,hB,hBdata⟩ :=
    exists_local_uniform_sourceCriticalGapQuotient hp hp1 φ hreal
  obtain ⟨_,_,VR,hVRopen,hφVR,R,hR,hRdata⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ
      (by norm_num : (0:ℝ) < 1)
  let C := B*R
  have hC : 0 ≤ C := mul_nonneg hB hR
  let δ := ε/(2*(C+1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδbound : C*δ ≤ ε/2 := by
    have hδeq : δ*(2*(C+1)) = ε := by
      dsimp [δ]
      field_simp
    nlinarith [hδ.le]
  obtain ⟨Nγ,_,Vγ,hVγopen,hφVγ,_,_,hγdata⟩ :=
    exists_uniform_small_sourcePeriodicGapDisplacement hp hp1 φ hδ
  obtain ⟨Nm,_,Vm,hVmopen,hφVm,_,_,hmdata⟩ :=
    exists_uniform_small_sourcePeriodicMidpointDisplacement hp hp1 φ
      (half_pos hε)
  obtain ⟨W,hWopen,hWreal,heq⟩ :=
    exists_global_sourceCriticalDisplacement_eq_midpoint_add_offset hp hp1
  let M := max Nγ Nm
  let s := Finset.Icc (-(M : ℤ)) (M : ℤ)
  let V := VB ∩ VR ∩ Vγ ∩ Vm ∩ W
  have hVopen : IsOpen V :=
    (((hVBopen.inter hVRopen).inter hVγopen).inter hVmopen).inter hWopen
  have hφV : φ ∈ V :=
    ⟨⟨⟨⟨hφVB,hφVR⟩,hφVγ⟩,hφVm⟩,hWreal hreal⟩
  refine ⟨s,V,hVopen,hφV,?_⟩
  intro ψ hψ
  obtain ⟨⟨⟨⟨hψB,hψR⟩,hψγ⟩,hψm⟩,hψW⟩ := hψ
  have hBψ := (hBdata ψ hψB).1
  have hRψ := (hRdata ψ hψR).1
  have hγtail := (hγdata ψ hψγ).2 M (le_max_left _ _)
  have hmtail := (hmdata ψ hψm).2 M (le_max_right _ _)
  have htail := norm_sourceCriticalGapSquareOffset_sub_truncate_le
    hp hp1 ψ s
  have hoffset : ‖sourceCriticalGapSquareOffset hp hp1 ψ -
      Coeff.truncate s (sourceCriticalGapSquareOffset hp hp1 ψ)‖ ≤
        C*δ := by
    calc
      _ ≤ ‖sourceCriticalGapQuotient hp hp1 ψ‖ *
          ‖sourcePeriodicGapDisplacement hp hp1 ψ‖ *
            ‖sourcePeriodicGapDisplacement hp hp1 ψ -
              Coeff.truncate s (sourcePeriodicGapDisplacement hp hp1 ψ)‖ := htail
      _ ≤ C*δ := by
        dsimp [C]
        gcongr
  rw [heq ψ hψW, Coeff.truncate_add]
  have hdecomp :
      sourcePeriodicMidpointDisplacement hp hp1 ψ +
        sourceCriticalGapSquareOffset hp hp1 ψ -
          (Coeff.truncate s (sourcePeriodicMidpointDisplacement hp hp1 ψ) +
            Coeff.truncate s (sourceCriticalGapSquareOffset hp hp1 ψ)) =
      (sourcePeriodicMidpointDisplacement hp hp1 ψ -
        Coeff.truncate s (sourcePeriodicMidpointDisplacement hp hp1 ψ)) +
      (sourceCriticalGapSquareOffset hp hp1 ψ -
        Coeff.truncate s (sourceCriticalGapSquareOffset hp hp1 ψ)) := by abel
  rw [hdecomp]
  calc
    _ ≤ ‖sourcePeriodicMidpointDisplacement hp hp1 ψ -
          Coeff.truncate s (sourcePeriodicMidpointDisplacement hp hp1 ψ)‖ +
        ‖sourceCriticalGapSquareOffset hp hp1 ψ -
          Coeff.truncate s (sourceCriticalGapSquareOffset hp hp1 ψ)‖ :=
      norm_add_le _ _
    _ ≤ ε/2 + C*δ := add_le_add hmtail hoffset
    _ ≤ ε := by linarith

/-- The critical displacement sequence is continuous in the full
`ℓp` norm at every real-type source. -/
theorem continuousAt_sourceCriticalDisplacement_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p φ)) :
    ContinuousAt (sourceCriticalDisplacement hp hp1) φ := by
  let F : CoeffPair p →L[ℂ] pairParitySubspace (p := p) 0 :=
    (periodOnePotential (p := p)).codRestrict _ periodOnePotential_mem
  have hcoord (n : ℤ) : ContinuousAt
      (fun ψ : CoeffPair p => sourceCriticalDisplacement hp hp1 ψ n) φ := by
    exact (continuousAt_canonicalCriticalDisplacement_apply_of_realType
      hp hp1 (F φ) (isRealType_periodOnePotential φ hreal) n).comp
        F.continuous.continuousAt
  exact Coeff.continuousAt_of_coordinatewise_of_uniform_tails
    (sourceCriticalDisplacement hp hp1) φ hcoord
      (exists_local_sourceCriticalDisplacement_uniform_tails
        hp hp1 φ hreal)

end NLS.ZakharovShabat
