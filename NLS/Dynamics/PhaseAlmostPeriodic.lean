import NLS.Dynamics.BohrAlmostPeriodic
import NLS.Dynamics.HamiltonianPhaseFlow
import NLS.SequenceSpaces.DominatedCompactness

/-! # Uniform almost periodicity of finite-exponent phase orbits

Arbitrary real frequencies give common uniform return times for both
Birkhoff components. The result includes the Hamiltonian time orientation
and continuous changes of coordinates.
-/

noncomputable section
open Set Metric
open scoped ENNReal
namespace NLS
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace Coeff

/-- The full norm compact set dominated coefficientwise by one finite-exponent sequence. -/
theorem isCompact_dominatedBox (hp : p ≠ ⊤) (a : Coeff p) :
    IsCompact {b : Coeff p | ∀ n : ℤ, ‖b n‖ ≤ ‖a n‖} := by
  apply isCompact_of_isClosed_of_majorant hp a
  · simp only [ofPred_forall]
    exact isClosed_iInter (fun n => isClosed_le
      ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) p n).continuous.norm) continuous_const)
  · exact fun _ hb => hb

/-- Every diagonal phase orbit at finite exponent is uniformly almost periodic,
including arbitrary unbounded real frequencies. -/
theorem bohrAlmostPeriodic_phaseFlow (hp : p ≠ ⊤) (ω : ℤ → ℝ) (a : Coeff p) :
    Dynamics.BohrAlmostPeriodic (fun t : ℝ => phaseFlow ω t a) := by
  apply Dynamics.bohrAlmostPeriodic_of_totallyBounded_range
  · exact (continuous_phaseFlow hp ω).comp (continuous_id.prodMk continuous_const)
  · apply (isCompact_dominatedBox hp a).totallyBounded.subset
    rintro _ ⟨t,rfl⟩ n
    exact (norm_phaseMultiply_apply (fun n => t*ω n) a n).le
  · intro t u v
    have h := (phaseFlow ω t).isometry.dist_eq (phaseFlow ω u a) (phaseFlow ω v a)
    rwa [phaseFlow_add,phaseFlow_add] at h

end Coeff
namespace Birkhoff

/-- The product majorant set is compact and contains every phase of the orbit. -/
theorem isCompact_phaseBox (hp : p ≠ ⊤) (z : Coeff p × Coeff p) :
    IsCompact ({a : Coeff p | ∀ n : ℤ, ‖a n‖ ≤ ‖z.1 n‖} ×ˢ
      {b : Coeff p | ∀ n : ℤ, ‖b n‖ ≤ ‖z.2 n‖}) :=
  (Coeff.isCompact_dominatedBox hp z.1).prod (Coeff.isCompact_dominatedBox hp z.2)

/-- Opposite phase rotations act isometrically in the actual product norm. -/
theorem isometry_phaseFlow (ω : ℤ → ℝ) (t : ℝ) :
    Isometry (phaseFlow (p := p) ω t) := by
  apply Isometry.of_dist_eq
  intro z w
  simp only [phaseFlow, Prod.dist_eq]
  rw [(Coeff.phaseFlow ω t).isometry.dist_eq,
    (Coeff.phaseFlow ω (-t)).isometry.dist_eq]

/-- The two phase components have common relatively dense uniform return times. -/
theorem bohrAlmostPeriodic_phaseFlow (hp : p ≠ ⊤) (ω : ℤ → ℝ)
    (z : Coeff p × Coeff p) :
    Dynamics.BohrAlmostPeriodic (fun t : ℝ => phaseFlow ω t z) := by
  apply Dynamics.bohrAlmostPeriodic_of_totallyBounded_range
  · exact ((continuous_phaseFlow_family hp (fun _ : Unit => ω) (fun _ => z)
      (fun _ => continuous_const) continuous_const).comp
      (continuous_id.prodMk (continuous_const (y := ()))))
  · apply ((Coeff.isCompact_dominatedBox hp z.1).prod
      (Coeff.isCompact_dominatedBox hp z.2)).totallyBounded.subset
    rintro _ ⟨t,rfl⟩
    exact ⟨fun n => (Coeff.norm_phaseMultiply_apply (fun n => t*ω n) z.1 n).le,
      fun n => (Coeff.norm_phaseMultiply_apply (fun n => -t*ω n) z.2 n).le⟩
  · intro t u v
    have h := (isometry_phaseFlow ω t).dist_eq (phaseFlow ω u z) (phaseFlow ω v z)
    rwa [phaseFlow_add,phaseFlow_add] at h

/-- The Hamiltonian time orientation has the same uniform recurrence property. -/
theorem bohrAlmostPeriodic_hamiltonianPhaseFlow (hp : p ≠ ⊤) (ω : ℤ → ℝ)
    (z : Coeff p × Coeff p) :
    Dynamics.BohrAlmostPeriodic (fun t : ℝ => hamiltonianPhaseFlow ω t z) := by
  have hf := bohrAlmostPeriodic_phaseFlow hp ω z
  apply Dynamics.bohrAlmostPeriodic_of_totallyBounded_range
  · exact hf.continuous.comp continuous_neg
  · apply (isCompact_phaseBox hp z).totallyBounded.subset
    rintro _ ⟨t,rfl⟩
    exact ⟨fun n => (Coeff.norm_phaseMultiply_apply (fun n => -t*ω n) z.1 n).le,
      fun n => (Coeff.norm_phaseMultiply_apply (fun n => -(-t)*ω n) z.2 n).le⟩
  · intro t u v
    have h := (isometry_phaseFlow ω (-t)).dist_eq
      (hamiltonianPhaseFlow ω u z) (hamiltonianPhaseFlow ω v z)
    simpa only [hamiltonianPhaseFlow,phaseFlow_add,neg_add] using h

/-- A continuous inverse coordinate map preserves uniform recurrence on a phase orbit. -/
theorem bohrAlmostPeriodic_hamiltonianPhaseFlow_comp
    {Y : Type*} [PseudoMetricSpace Y] (hp : p ≠ ⊤) (ω : ℤ → ℝ)
    (z : Coeff p × Coeff p) (g : Coeff p × Coeff p → Y) (hg : Continuous g) :
    Dynamics.BohrAlmostPeriodic (fun t : ℝ => g (hamiltonianPhaseFlow ω t z)) := by
  exact (bohrAlmostPeriodic_hamiltonianPhaseFlow hp ω z).comp_continuousOn_compact
    _ (isCompact_phaseBox hp z)
    (fun t => ⟨fun n => (Coeff.norm_phaseMultiply_apply (fun n => -t*ω n) z.1 n).le,
      fun n => (Coeff.norm_phaseMultiply_apply (fun n => -(-t)*ω n) z.2 n).le⟩)
    g hg.continuousOn

end Birkhoff
end NLS
