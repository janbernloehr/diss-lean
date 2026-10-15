import NLS.ZakharovShabat.SourceSection21Moments
import NLS.ZakharovShabat.SourceHamiltonianOriginal
import NLS.ZakharovShabat.SourceRenormalizedHamiltonianProposition21_3

/-! # The cubic Hamiltonian on the original common source domain

One connected source neighborhood carries every primitive-power moment,
the absolutely and locally uniformly convergent cubic sum, and the same
original action Hamiltonian. The latter's gradient is the Section 20
moment frequency throughout that complex source neighborhood.
-/
noncomputable section
open Set Metric Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩
local instance : (4 : ℝ≥0∞).HolderTriple 4 2 := (ENNReal.holderTriple_iff _ _ _).mpr (by
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_add])
variable {W₀ W V Wa B U Wp T : Set (CoeffPair 4)}
  {s : (n : ℤ) → CoeffPair 4 → DeletedCoeff 4 n}
  {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
  {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
  {L : Set (Coeff 2)} {F : Coeff 2 → Coeff 2} {H : Coeff 2 → ℂ}

/-- Proposition 21.3 on one original-family domain, retaining the original
moment package and an already chosen action Hamiltonian and frequency. -/
structure SourceSection21HamiltonianData (Q : SourceSection20Data D A B U)
    (P : SourcePrimitivePowerAtlas (by simp) (by norm_num) Wp)
    (E : SourceOriginalHamiltonianData D L F H) (T : Set (CoeffPair 4)) : Prop
    extends SourceSection21MomentData Q P T where
  analytic : AnalyticOnNhd ℂ P.renormalizedHamiltonian T
  summable : ∀ ψ ∈ T, Summable (fun n => ‖P.moment n 3 ψ‖)
  locally_uniform_sum : TendstoLocallyUniformlyOn
    (fun (N : ℕ) ψ => -(4/3:ℂ)*∑ n ∈ Finset.Icc (-(N:ℤ)) N, P.moment n 3 ψ)
    P.renormalizedHamiltonian atTop T
  action_mem : ∀ ψ ∈ T, sourceActionSequence (q := 2) (by simp) (by norm_num) s ψ ∈ L
  action_hamiltonian : ∀ ψ ∈ T,
    H (sourceActionSequence (q := 2) (by simp) (by norm_num) s ψ) = P.renormalizedHamiltonian ψ

variable {Q : SourceSection20Data D A B U}
  {P : SourcePrimitivePowerAtlas (by simp) (by norm_num) Wp}
  {E : SourceOriginalHamiltonianData D L F H}

/-- Keep every moment bound and identify the cubic sum with the already
chosen original Hamiltonian on one connected complex source neighborhood. -/
theorem SourceSection21MomentData.exists_hamiltonian_domain
    (M : SourceSection21MomentData Q P T) (E : SourceOriginalHamiltonianData D L F H) :
    ∃ S : Set (CoeffPair 4), SourceSection21HamiltonianData Q P E S ∧ S ⊆ T := by
  let X := V ∩ sourceActionSequence (q := 2) (by simp) (by norm_num) s ⁻¹' L
  have hX : IsOpen X := D.complex.actionSequence_analytic.continuousOn.isOpen_inter_preimage
    D.complex.source_open E.frequency.isOpen
  have hrX : realTypeSourceLocus 4 ⊆ X :=
    fun ψ hψ => ⟨D.complex.real_subset hψ,E.frequency.real_actions_mem ⟨ψ,hψ⟩⟩
  have hHX : AnalyticOnNhd ℂ (fun ψ => H (sourceActionSequence (q := 2) (by simp) (by norm_num) s ψ)) X :=
    fun ψ hψ => (E.analytic _ hψ.2).comp (D.complex.actionSequence_analytic ψ hψ.1)
  obtain ⟨Y,hY,_,hrY,_,ha,hs,hconv⟩ := P.exists_renormalizedHamiltonian_analytic
  let S := connectedComponentIn (T ∩ (Y ∩ X)) (0 : CoeffPair 4)
  have ho : IsOpen S := (M.source_open.inter (hY.inter hX)).connectedComponentIn
  have hsub : S ⊆ T ∩ (Y ∩ X) := connectedComponentIn_subset _ _
  have hz : (0 : CoeffPair 4) ∈ realTypeSourceLocus 4 := by simp [realTypeSourceLocus]
  have hr : realTypeSourceLocus 4 ⊆ S :=
    isConnected_realTypeSourceLocus.isPreconnected.subset_connectedComponentIn hz
      (fun ψ hψ => ⟨M.real_subset hψ,hrY hψ,hrX hψ⟩)
  have hc : IsConnected S := isConnected_connectedComponentIn_iff.mpr
    ⟨M.real_subset hz,hrY hz,hrX hz⟩
  have hSY : S ⊆ Y := fun ψ hψ => (hsub hψ).2.1
  have hSX : S ⊆ X := fun ψ hψ => (hsub hψ).2.2
  have hST : S ⊆ T := fun ψ hψ => (hsub hψ).1
  refine ⟨S,{
    toSourceSection21MomentData := M.restrict S ho hc hr hST
    analytic := ha.mono hSY
    summable := fun ψ hψ => hs ψ (hSY hψ)
    locally_uniform_sum := hconv.mono hSY
    action_mem := fun ψ hψ => (hSX hψ).2
    action_hamiltonian := ?_
  },hST⟩
  apply eqOn_of_analytic_of_sourceFiniteGap (by simp) (by norm_num) ho hc hr
    (hHX.mono hSX) (ha.mono hSY)
  intro φ hf
  obtain ⟨Wb,Pb,he⟩ := E.spectral
  exact (he φ).trans ((Pb.renormalizedHamiltonian_eq_finiteGap φ hf).trans
    (P.renormalizedHamiltonian_eq_finiteGap φ hf).symm)

namespace SourceSection21HamiltonianData
variable (M : SourceSection21HamiltonianData Q P E T)
include M

/-- The cubic series has its exact negative coefficient and no summability premise. -/
theorem hamiltonian_hasSum (ψ : CoeffPair 4) (hψ : ψ ∈ T) :
    HasSum (fun n => -(4/3:ℂ)*P.moment n 3 ψ) (P.renormalizedHamiltonian ψ) :=
  (M.summable ψ hψ).of_norm.hasSum.mul_left _

/-- The actual cubic Hamiltonian is real, nonpositive, and vanishes exactly at zero. -/
theorem real_sign (φ : realTypeSourceSubmodule 4) :
    (P.renormalizedHamiltonian φ.val).re ≤ 0 ∧ (P.renormalizedHamiltonian φ.val).im = 0 ∧
      (P.renormalizedHamiltonian φ.val = 0 ↔ φ = 0) := by
  rw [← M.action_hamiltonian φ.val (M.real_subset φ.property)]
  exact E.source_sign φ

/-- The restriction is real analytic on the whole real FL⁴ source space. -/
theorem real_analytic : AnalyticOnNhd ℝ
    (fun φ : realTypeSourceSubmodule 4 => P.renormalizedHamiltonian φ.val) univ := by
  intro φ _
  exact ((M.analytic φ.val (M.real_subset φ.property)).restrictScalars (𝕜 := ℝ)).comp
    ((realTypeSourceSubmodule 4).subtypeL.analyticAt φ)

/-- Every assertion of Proposition 21.3 concerns these same original moments and Hamiltonian. -/
theorem proposition21_3 :
    AnalyticOnNhd ℂ P.renormalizedHamiltonian T ∧
    (∀ ψ ∈ T, Summable (fun n => ‖P.moment n 3 ψ‖)) ∧
    TendstoLocallyUniformlyOn
      (fun (N : ℕ) ψ => -(4/3:ℂ)*∑ n ∈ Finset.Icc (-(N:ℤ)) N, P.moment n 3 ψ)
      P.renormalizedHamiltonian atTop T ∧
    AnalyticOnNhd ℝ (fun φ : realTypeSourceSubmodule 4 => P.renormalizedHamiltonian φ.val) univ ∧
    ∀ φ : realTypeSourceSubmodule 4,
      (P.renormalizedHamiltonian φ.val).re ≤ 0 ∧ (P.renormalizedHamiltonian φ.val).im = 0 ∧
        (P.renormalizedHamiltonian φ.val = 0 ↔ φ = 0) :=
  ⟨M.analytic,M.summable,M.locally_uniform_sum,M.real_analytic,M.real_sign⟩

/-- The same cubic sum agrees with the full physical H¹ correction, including all weighted actions. -/
theorem physical_identity (a : realTypeSobolevSourceLocus) :
    P.renormalizedHamiltonian (sobolevSourceFL4 a.val) =
      periodOneSobolevHamiltonian a.val-2*(periodOneSobolevMass a.val)^2-
        ∑' n : ℤ, sourceSobolevWeightedAction a.val n := by
  have he := M.action_hamiltonian _ (M.real_subset (realSobolevSourceFL4 a).property)
  exact he.symm.trans (E.physical_identity a)

/-- The original Section 20 frequency is the action gradient of this same Hamiltonian. -/
theorem action_frequency (ψ : CoeffPair 4) (hψ : ψ ∈ T) (n : ℤ) :
    F (sourceActionSequence (q := 2) (by simp) (by norm_num) s ψ) n = A.renormalizedFrequency n ψ := by
  have hf : AnalyticOnNhd ℂ
      (fun χ => F (sourceActionSequence (q := 2) (by simp) (by norm_num) s χ) n) T := by
    intro χ hχ
    exact ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 n).analyticAt _).comp
      ((E.frequency.analytic _ (M.action_mem χ hχ)).comp
        (D.complex.actionSequence_analytic χ (Q.original_subset (M.source_subset hχ))))
  exact eqOn_of_analytic_of_sourceFiniteGap (by simp) (by norm_num) M.source_open M.connected
    M.real_subset hf ((Q.frequency_analytic n).mono M.source_subset)
    (fun φ _ => Q.action_frequency E.frequency φ n) hψ

/-- The full ℓ² frequency sequence agrees, not only individual coordinate values. -/
theorem action_frequency_sequence (ψ : CoeffPair 4) (hψ : ψ ∈ T) :
    F (sourceActionSequence (q := 2) (by simp) (by norm_num) s ψ) = A.frequencySequence 2 ψ := by
  ext n
  rw [(Q.sequence 2 (by norm_num) (by norm_num) (by norm_num)).1 ψ (M.source_subset hψ) n]
  exact M.action_frequency ψ hψ n

/-- The full complex source derivative pairs the retained frequency with the actual action derivative. -/
theorem source_fderiv (ψ h : CoeffPair 4) (hψ : ψ ∈ T) :
    fderiv ℂ P.renormalizedHamiltonian ψ h = Coeff.dualPairing (A.frequencySequence 2 ψ)
      (fderiv ℂ (sourceActionSequence (q := 2) (by simp) (by norm_num) s) ψ h) := by
  have he : (fun χ => H (sourceActionSequence (q := 2) (by simp) (by norm_num) s χ)) =ᶠ[𝓝 ψ]
      P.renormalizedHamiltonian := by
    filter_upwards [M.source_open.mem_nhds hψ] with χ hχ
    exact M.action_hamiltonian χ hχ
  have hc : fderiv ℂ (fun χ => H (sourceActionSequence (q := 2) (by simp) (by norm_num) s χ)) ψ =
      (fderiv ℂ H (sourceActionSequence (q := 2) (by simp) (by norm_num) s ψ)).comp
        (fderiv ℂ (sourceActionSequence (q := 2) (by simp) (by norm_num) s) ψ) := by
    simpa only [Function.comp_def] using! fderiv_comp ψ
      (E.analytic _ (M.action_mem ψ hψ)).differentiableAt
      (D.complex.actionSequence_analytic ψ (Q.original_subset (M.source_subset hψ))).differentiableAt
  rw [← he.fderiv_eq,hc,ContinuousLinearMap.comp_apply,Coeff.fderiv_eq_dualPairing_scalarGradient,
    ← E.gradient_eq (M.action_mem ψ hψ),M.action_frequency_sequence ψ hψ]

/-- The same full derivative is an absolutely convergent frequency-weighted action series. -/
theorem source_derivative_series (ψ h : CoeffPair 4) (hψ : ψ ∈ T) :
    Summable (fun n : ℤ => ‖A.renormalizedFrequency n ψ *
      fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) ψ h‖) ∧
    fderiv ℂ P.renormalizedHamiltonian ψ h = ∑' n : ℤ, A.renormalizedFrequency n ψ *
      fderiv ℂ (sourceComplexAction (by simp) (by norm_num) n) ψ h := by
  have hf (n : ℤ) := (Q.sequence 2 (by norm_num) (by norm_num) (by norm_num)).1
    ψ (M.source_subset hψ) n
  have hd (n : ℤ) := D.complex.actionSequence_fderiv_apply (q := 2) ψ
    (Q.original_subset (M.source_subset hψ)) h n
  constructor
  · simpa only [hf,hd] using Coeff.summable_norm_dualPairing (A.frequencySequence 2 ψ)
      (fderiv ℂ (sourceActionSequence (q := 2) (by simp) (by norm_num) s) ψ h)
  · rw [M.source_fderiv ψ h hψ,Coeff.dualPairing_apply]
    apply tsum_congr
    intro n
    rw [hf,hd]

end SourceSection21HamiltonianData
end NLS.ZakharovShabat
