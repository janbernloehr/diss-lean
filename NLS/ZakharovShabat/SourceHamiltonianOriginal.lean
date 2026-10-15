import NLS.ZakharovShabat.SourceFrequencyOriginalRestriction
import NLS.ZakharovShabat.SourceHamiltonianActionConcavity
import NLS.ZakharovShabat.SourceSobolevHamiltonianIdentification

/-!
# The original Hamiltonian with the same action frequency

Theorem 18.3 uses one actual Hamiltonian on a common connected action domain.
Its gradient is the frequency from Theorem 18.1, and the physical identity
holds for every real H¹ source, including the weighted action subtraction.
-/
noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4 : ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])
variable {W₀ W V : Set (CoeffPair 4)} {s : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n}

/-- One original action Hamiltonian, retaining all frequency conclusions. -/
structure SourceOriginalHamiltonianData
    (D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s)
    (T : Set (Coeff 2)) (F : Coeff 2 → Coeff 2) (H : Coeff 2 → ℂ) : Prop where
  frequency : SourceOriginalFrequencyData D T F
  analytic : AnalyticOnNhd ℂ H T
  spectral : ∃ Wa : Set (CoeffPair 4), ∃ A : SourcePrimitivePowerAtlas (by simp) (by norm_num) Wa,
    ∀ φ : realTypeSourceSubmodule 4,
      H (sourceActionSequence (q := 2) (by simp) (by norm_num) s φ.val) = A.renormalizedHamiltonian φ.val
  physical : ∀ a : realTypeSobolevSourceLocus,
    H (sourceActionSequence (q := 2) (by simp) (by norm_num) s (sobolevSourceFL4 a.val)) =
      sourceSobolevPhysicalCorrection a.val
  sign : ∀ b ∈ T, b ∈ Coeff.nonnegativeLocus 2 →
    (H b).re ≤ 0 ∧ (H b).im = 0 ∧ (H b = 0 ↔ b = 0)
  gradient_eq : EqOn F (Coeff.scalarGradient H) T
  hessian_zero : ∀ v w : Coeff 2, fderiv ℂ (fderiv ℂ H) 0 v w = -2 * Coeff.dualPairing v w
  concavity : ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : Coeff 2) r ⊆ T ∧
    ∀ b ∈ Metric.ball (0 : Coeff 2) r, ∀ J : RealCoeff 2,
      (fderiv ℂ (fderiv ℂ H) b (RealCoeff.complexCLM 2 J) (RealCoeff.complexCLM 2 J)).re ≤ -‖J‖^2

/-- The original Hamiltonian can be attached to any already constructed
original frequency, preserving that map and all its conclusions. -/
theorem SourceOriginalFrequencyData.exists_original_hamiltonian
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {U : Set (Coeff 2)} {F : Coeff 2 → Coeff 2} (E : SourceOriginalFrequencyData D U F) :
    ∃ T : Set (Coeff 2), ∃ H : Coeff 2 → ℂ, T ⊆ U ∧ SourceOriginalHamiltonianData D T F H := by
  obtain ⟨Wa,A,X₀,B,X,t,C,Y,P,u,Ba,hs,hP,hrP,L,H,hL,_,hcenter,_,hH,hrec,hsign,hG,hGrec,_,hess,r,hr,_,hbound⟩ :=
    exists_sourceHamiltonian_action_extension_with_concavity
  have he (φ : realTypeSourceSubmodule 4) : sourceActionSequence (q := 2) (by simp) (by norm_num) s φ.val =
      sourceActionSequence (by simp) (by norm_num) t φ.val :=
    D.actionSequence_eq C φ.val (D.complex.real_subset φ.property) (C.real_subset φ.property)
  have hcenter' (φ : realTypeSourceSubmodule 4) : sourceActionSequence (q := 2) (by simp) (by norm_num) s φ.val ∈ L :=
    (he φ).symm ▸ hcenter φ
  have hrec' (φ : realTypeSourceSubmodule 4) :
      H (sourceActionSequence (q := 2) (by simp) (by norm_num) s φ.val) = A.renormalizedHamiltonian φ.val := by
    rw [he φ]
    exact hrec φ
  let T := connectedComponentIn (U ∩ L) (0 : Coeff 2)
  have hT : IsOpen T := (E.isOpen.inter hL).connectedComponentIn
  have hsub : T ⊆ U ∩ L := connectedComponentIn_subset _ _
  have hcenterBoth : ∀ φ : realTypeSourceSubmodule 4,
      sourceActionSequence (q := 2) (by simp) (by norm_num) s φ.val ∈ U ∩ L :=
    fun φ => ⟨E.real_actions_mem φ,hcenter' φ⟩
  have hreal : ∀ φ : realTypeSourceSubmodule 4,
      sourceActionSequence (q := 2) (by simp) (by norm_num) s φ.val ∈ T :=
    D.complex.real_actions_mem_zero_component hcenterBoth
  have hz : (0 : Coeff 2) ∈ T := by
    simpa only [ZeroMemClass.coe_zero,D.complex.actionSequence_zero] using hreal 0
  have hsame : EqOn F (Coeff.scalarGradient H) T :=
    E.eqOn_component_of_original_recovery (by norm_num) Ba hs.toSourcePsiIsolatingComplexExtension
      L hL (Coeff.scalarGradient H) hG hcenter' (fun φ n => by rw [he φ]; exact hGrec φ n)
  obtain ⟨δ,hδ,hδT⟩ := Metric.mem_nhds_iff.mp (hT.mem_nhds hz)
  refine ⟨T,H,fun _ hb => (hsub hb).1,
    E.restrict (by norm_num) T hT isPreconnected_connectedComponentIn
      (fun _ hb => (hsub hb).1) hreal,
    hH.mono (fun _ hb => (hsub hb).2),⟨Wa,A,hrec'⟩,?_,
    fun b hb => hsign b (hsub hb).2,hsame,hess,
    min r δ,lt_min hr hδ,?_,?_⟩
  · intro a
    exact (hrec' ⟨sobolevSourceFL4 a.val,(realSobolevSourceFL4 a).property⟩).trans
      (A.renormalizedHamiltonian_eq_sobolevPhysicalCorrection a)
  · exact (Metric.ball_subset_ball (min_le_right r δ)).trans hδT
  · intro b hb J
    exact hbound b (Metric.ball_subset_ball (min_le_left r δ) hb) J

namespace SourceOriginalHamiltonianData
variable {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {T : Set (Coeff 2)} {F : Coeff 2 → Coeff 2} {H : Coeff 2 → ℂ}

/-- The actual FL⁴ extension is analytic on an open complex neighborhood
of the entire real locus, using the original action map. -/
theorem source_extension (Q : SourceOriginalHamiltonianData D T F H) :
    ∃ X : Set (CoeffPair 4), IsOpen X ∧ realTypeSourceLocus 4 ⊆ X ∧ X ⊆ V ∧
      AnalyticOnNhd ℂ (fun φ => H (sourceActionSequence (q := 2) (by simp) (by norm_num) s φ)) X := by
  let X := V ∩ sourceActionSequence (q := 2) (by simp) (by norm_num) s ⁻¹' T
  refine ⟨X,D.complex.actionSequence_analytic.continuousOn.isOpen_inter_preimage
    D.complex.source_open Q.frequency.isOpen,
    fun φ hφ => ⟨D.complex.real_subset hφ,Q.frequency.real_actions_mem ⟨φ,hφ⟩⟩,inter_subset_left,?_⟩
  intro φ hφ
  exact (Q.analytic _ hφ.2).comp (D.complex.actionSequence_analytic φ hφ.1)

/-- Theorem 18.3(i): the original FL⁴ extension is real, nonpositive,
and vanishes exactly at the zero source. -/
theorem source_sign (Q : SourceOriginalHamiltonianData D T F H) (φ : realTypeSourceSubmodule 4) :
    (H (sourceActionSequence (q := 2) (by simp) (by norm_num) s φ.val)).re ≤ 0 ∧
    (H (sourceActionSequence (q := 2) (by simp) (by norm_num) s φ.val)).im = 0 ∧
    (H (sourceActionSequence (q := 2) (by simp) (by norm_num) s φ.val) = 0 ↔ φ = 0) := by
  obtain ⟨Wa,A,hrec⟩ := Q.spectral
  rw [hrec φ]
  exact ⟨(A.real_renormalizedHamiltonian_nonpos φ).1,
    (A.real_renormalizedHamiltonian_nonpos φ).2,A.real_renormalizedHamiltonian_eq_zero_iff φ⟩

/-- The physical identity retains the literal absolutely convergent weighted actions. -/
theorem physical_identity (Q : SourceOriginalHamiltonianData D T F H) (a : realTypeSobolevSourceLocus) :
    H (sourceActionSequence (q := 2) (by simp) (by norm_num) s (sobolevSourceFL4 a.val)) =
      periodOneSobolevHamiltonian a.val - 2*(periodOneSobolevMass a.val)^2 -
        ∑' n : ℤ, sourceSobolevWeightedAction a.val n := by
  rw [Q.physical a,sourceSobolevPhysicalCorrection,sourceSobolevWeightedActionSum_eq_tsum a.val a.property]

end SourceOriginalHamiltonianData

/-- Construct Theorem 18.3 together with the original family and its frequency. -/
theorem sourceSection18_original_hamiltonian :
    ∃ W₀ W V : Set (CoeffPair 4), ∃ s : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n,
    ∃ D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s,
    ∃ T : Set (Coeff 2), ∃ F : Coeff 2 → Coeff 2, ∃ H : Coeff 2 → ℂ,
      SourceOriginalHamiltonianData D T F H := by
  obtain ⟨W₀,W,V,s,D⟩ := sourceSection17_original (p := 4) (by simp) (by norm_num)
  obtain ⟨U,F,E⟩ := D.exists_frequency_asymptotic (q := 2) (by norm_num)
  obtain ⟨T,H,_,Q⟩ := E.exists_original_hamiltonian
  exact ⟨W₀,W,V,s,D,T,F,H,Q⟩

end NLS.ZakharovShabat
