import NLS.MKdV.MiuraEvenFrequencyOnOpenAngles
import NLS.MKdV.MiuraHigherSobolevOpenAngleDensity
import NLS.SequenceSpaces.PhysicalSobolevDenseInclusion

/-! # The actual restricted even NLS frequencies on the sharp real H^s domain

An extension is specified solely by continuity and agreement with the
original S_(2s+2) angle bracket on real H^(s+1) open-angle inputs. Density
makes it unique. The proved bracket comparison supplies existence and a
holomorphic germ at every real H^s profile, including all closed actions.
-/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem miuraRealSobolevLower_eq_physicalInclusion (s : ℕ) :
    miuraRealSobolevLower s =
      WeightedCoeff.physicalSobolevInclusion (show (s : ℝ) ≤ ((s+1 : ℕ) : ℝ) by exact_mod_cast (by omega : s ≤ s+1)) := by
  funext a
  apply Subtype.ext
  apply Subtype.ext
  funext j
  change (hierarchySobolevInclusion (s+1) s (by omega) a.val).val j = _
  rw [hierarchySobolevInclusion_apply,WeightedCoeff.physicalSobolevInclusion_apply]

theorem continuous_miuraRealSobolevLower (s : ℕ) : Continuous (miuraRealSobolevLower s) := by
  rw [miuraRealSobolevLower_eq_physicalInclusion]
  exact ContinuousLinearMap.continuous _

theorem denseRange_miuraRealSobolevLower (s : ℕ) : DenseRange (miuraRealSobolevLower s) := by
  rw [miuraRealSobolevLower_eq_physicalInclusion]
  exact WeightedCoeff.physicalSobolevInclusion_denseRange _

/-- The NLS frequency extension is characterized by its original
Hamiltonian bracket, without a Hill frequency in the definition. -/
def IsMiuraOriginalEvenFrequencyExtension (s n : ℕ) (f : MiuraRealSobolevSource s → ℂ) : Prop :=
  Continuous f ∧ ∀ (a : MiuraRealSobolevSource (s+1))
    (hgap : canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (miuraSobolevActionSource (s+1) a.val)) (periodOnePotential_mem _) n ≠ 0),
      f (miuraRealSobolevLower s a) = miuraOriginalEvenNLSAngleFrequency s a n hgap

theorem miuraOriginalEvenFrequencyExtension_unique (s n : ℕ) (hn : 1 ≤ n)
    (f g : MiuraRealSobolevSource s → ℂ)
    (hf : IsMiuraOriginalEvenFrequencyExtension s n f) (hg : IsMiuraOriginalEvenFrequencyExtension s n g) : f = g := by
  have hc : IsClosed {a : MiuraRealSobolevSource (s+1) |
      f (miuraRealSobolevLower s a) = g (miuraRealSobolevLower s a)} :=
    isClosed_eq (hf.1.comp (continuous_miuraRealSobolevLower s))
      (hg.1.comp (continuous_miuraRealSobolevLower s))
  have hs : {a : MiuraRealSobolevSource (s+1) | canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (miuraSobolevActionSource (s+1) a.val)) (periodOnePotential_mem _) n ≠ 0} ⊆
      {a | f (miuraRealSobolevLower s a) = g (miuraRealSobolevLower s a)} := by
    intro a ha
    exact (hf.2 a ha).trans (hg.2 a ha).symm
  have hall (a : MiuraRealSobolevSource (s+1)) :
      f (miuraRealSobolevLower s a) = g (miuraRealSobolevLower s a) :=
    closure_minimal hs hc (dense_miuraHigherSobolev_open_angle (s+1) (by omega) n hn a)
  exact (denseRange_miuraRealSobolevLower s).equalizer hf.1 hg.1 (funext hall)

namespace MiuraNativeHamiltonianActionData

def sourceFrequency {s : ℕ} (D : MiuraNativeHamiltonianActionData s) (n : ℤ) (a : ScalarSobolev s) : ℂ :=
  D.frequency n (miuraNativeActionMeanMap s a)

theorem sourceFrequency_analyticAt {s : ℕ} (D : MiuraNativeHamiltonianActionData s) (n : ℤ)
    (a : MiuraRealSobolevSource s) : AnalyticAt ℂ (D.sourceFrequency n) a.val :=
  (D.frequency_analytic n _ (D.contains a)).comp (f := miuraNativeActionMeanMap s)
    (analyticAt_miuraNativeActionMeanMap s a)

theorem sourceFrequency_continuous {s : ℕ} (D : MiuraNativeHamiltonianActionData s) (n : ℤ) :
    Continuous (fun a : MiuraRealSobolevSource s => D.sourceFrequency n a.val) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  exact (D.sourceFrequency_analyticAt n a).continuousAt.comp continuous_subtype_val.continuousAt

theorem sourceFrequency_original_extension {s : ℕ} (D : MiuraNativeHamiltonianActionData s)
    (n : ℕ) (hn : 1 ≤ n) :
    IsMiuraOriginalEvenFrequencyExtension s n (fun a => D.sourceFrequency (n : ℤ) a.val) :=
  ⟨D.sourceFrequency_continuous n,fun a ha =>
    (miuraOriginalEvenNLSAngleFrequency_eq_Hill_frequency s D a n hn ha).symm⟩

end MiuraNativeHamiltonianActionData

/-- The actual original bracket has exactly one continuous extension to
ALL real H^s profiles. Closed selected actions are included in this domain. -/
theorem existsUnique_miuraOriginalEvenFrequencyExtension (s n : ℕ) (hn : 1 ≤ n) :
    ∃! f : MiuraRealSobolevSource s → ℂ, IsMiuraOriginalEvenFrequencyExtension s n f := by
  obtain ⟨D⟩ := nonempty_miuraNativeHamiltonianActionData s
  refine ⟨_,D.sourceFrequency_original_extension n hn,?_⟩
  intro f hf
  exact miuraOriginalEvenFrequencyExtension_unique s n hn f _ hf (D.sourceFrequency_original_extension n hn)

/-- The restricted original NLS frequency, characterized independently
by its actual S_(2s+2) angle bracket and unique continuous continuation. -/
def miuraOriginalEvenNLSFrequency (s n : ℕ) (hn : 1 ≤ n) : MiuraRealSobolevSource s → ℂ :=
  (existsUnique_miuraOriginalEvenFrequencyExtension s n hn).choose

theorem miuraOriginalEvenNLSFrequency_spec (s n : ℕ) (hn : 1 ≤ n) :
    IsMiuraOriginalEvenFrequencyExtension s n (miuraOriginalEvenNLSFrequency s n hn) :=
  (existsUnique_miuraOriginalEvenFrequencyExtension s n hn).choose_spec.1

/-- Corrected frequency comparison on the exact full original real H^s
source, for every hierarchy order and arbitrary closed-action pattern. -/
theorem miuraOriginalEvenNLSFrequency_eq_Hill_frequency (s n : ℕ) (hn : 1 ≤ n)
    (D : MiuraNativeHamiltonianActionData s) (a : MiuraRealSobolevSource s) :
    miuraOriginalEvenNLSFrequency s n hn a = D.frequency (n : ℤ) (miuraNativeActionMeanMap s a.val) := by
  have he := miuraOriginalEvenFrequencyExtension_unique s n hn _ _
    (miuraOriginalEvenNLSFrequency_spec s n hn) (D.sourceFrequency_original_extension n hn)
  exact congrFun he a

/-- One ambient complex function represents the original restricted
frequency on all real H^s profiles and is holomorphic near each of them. -/
theorem exists_analytic_miuraOriginalEvenNLSFrequency (s n : ℕ) (hn : 1 ≤ n) :
    ∃ f : ScalarSobolev s → ℂ, (∀ a : MiuraRealSobolevSource s, AnalyticAt ℂ f a.val) ∧
      ∀ a : MiuraRealSobolevSource s, f a.val = miuraOriginalEvenNLSFrequency s n hn a := by
  obtain ⟨D⟩ := nonempty_miuraNativeHamiltonianActionData s
  exact ⟨D.sourceFrequency n,D.sourceFrequency_analyticAt n,
    fun a => (miuraOriginalEvenNLSFrequency_eq_Hill_frequency s n hn D a).symm⟩

/-- One open complex source neighborhood contains the entire original
real H^s locus, including all closed-gap profiles. -/
theorem exists_common_open_analytic_miuraOriginalEvenNLSFrequency (s n : ℕ) (hn : 1 ≤ n) :
    ∃ U : Set (ScalarSobolev s), ∃ f : ScalarSobolev s → ℂ,
      IsOpen U ∧ (∀ a : MiuraRealSobolevSource s, a.val ∈ U) ∧ AnalyticOnNhd ℂ f U ∧
        ∀ a : MiuraRealSobolevSource s, f a.val = miuraOriginalEvenNLSFrequency s n hn a := by
  obtain ⟨f,hf,hrec⟩ := exists_analytic_miuraOriginalEvenNLSFrequency s n hn
  exact ⟨{a | AnalyticAt ℂ f a},f,isOpen_analyticAt ℂ f,hf,fun _ ha => ha,hrec⟩

end NLS.MKdV
