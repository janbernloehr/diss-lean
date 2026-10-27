import NLS.ZakharovShabat.PhysicalPeriodicEndpoints
import NLS.ZakharovShabat.SourcePeriodicOverview

/-! # Midpoints and gaps of the actual physical periodic endpoint labels -/
noncomputable section
set_option autoImplicit false
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat

def physicalPeriodicMidpoint (u : IntervalPairL2) (n : ℤ) : ℂ :=
  (physicalPeriodicLeft u n + physicalPeriodicRight u n)/2

def physicalPeriodicGap (u : IntervalPairL2) (n : ℤ) : ℂ :=
  physicalPeriodicRight u n - physicalPeriodicLeft u n

theorem physicalPeriodicMidpoint_eq_source (u : IntervalPairL2) (n : ℤ) :
    physicalPeriodicMidpoint u n = canonicalPeriodicMidpoint (by simp) (by norm_num)
      (periodOnePotential (sourcePhysicalL2Equiv.symm u)) (periodOnePotential_mem _) n := by
  simp only [physicalPeriodicMidpoint,canonicalPeriodicMidpoint,
    (physicalPeriodicEndpoints_eq_source u).1,(physicalPeriodicEndpoints_eq_source u).2]

theorem physicalPeriodicGap_eq_source (u : IntervalPairL2) (n : ℤ) :
    physicalPeriodicGap u n = canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sourcePhysicalL2Equiv.symm u)) (periodOnePotential_mem _) n := by
  simp only [physicalPeriodicGap,canonicalPeriodicGap,
    (physicalPeriodicEndpoints_eq_source u).1,(physicalPeriodicEndpoints_eq_source u).2]

/-- The actual midpoint displacement and gap are square summable, also for complex potentials. -/
theorem physicalPeriodicMidpointGap_memℓ2 (u : IntervalPairL2) :
    Memℓp (fun n => physicalPeriodicMidpoint u n-(Real.pi : ℂ)*n) 2 ∧
      Memℓp (physicalPeriodicGap u) 2 := by
  have h := physicalPeriodicEndpoints_spec u
  constructor
  · convert (h.left_displacement.add h.right_displacement).const_smul (1/2 : ℂ) using 1
    funext n
    dsimp [physicalPeriodicMidpoint]
    ring
  · convert h.right_displacement.sub h.left_displacement using 1
    funext n
    dsimp [physicalPeriodicGap]
    ring

/-- Square-summable sequences defined from the physical labels themselves. -/
def physicalPeriodicMidpointDisplacement (u : IntervalPairL2) : Coeff 2 :=
  ⟨fun n => physicalPeriodicMidpoint u n-(Real.pi : ℂ)*n,
    (physicalPeriodicMidpointGap_memℓ2 u).1⟩

def physicalPeriodicGapDisplacement (u : IntervalPairL2) : Coeff 2 :=
  ⟨physicalPeriodicGap u,(physicalPeriodicMidpointGap_memℓ2 u).2⟩

theorem physicalPeriodicMidpointDisplacement_eq_source (u : IntervalPairL2) :
    physicalPeriodicMidpointDisplacement u =
      sourcePeriodicMidpointDisplacement (by simp) (by norm_num) (sourcePhysicalL2Equiv.symm u) := by
  ext n
  change physicalPeriodicMidpoint u n-(Real.pi : ℂ)*n = _
  rw [physicalPeriodicMidpoint_eq_source,sourcePeriodicMidpointDisplacement_apply]

theorem physicalPeriodicGapDisplacement_eq_source (u : IntervalPairL2) :
    physicalPeriodicGapDisplacement u =
      sourcePeriodicGapDisplacement (by simp) (by norm_num) (sourcePhysicalL2Equiv.symm u) := by
  ext n
  exact (physicalPeriodicGap_eq_source u n).trans
    (sourcePeriodicGapDisplacement_apply (by simp) (by norm_num) _ n).symm

/-- One physical L2 neighborhood gives a common bound and arbitrarily small
square-summable tails for both midpoint and gap sequences, at every larger cutoff. -/
theorem exists_uniform_physicalPeriodicMidpointGap (u : IntervalPairL2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧ ∃ U : Set IntervalPairL2, IsOpen U ∧ u ∈ U ∧
      ∃ R : ℝ, 0 < R ∧ ∀ v ∈ U,
        ‖physicalPeriodicMidpointDisplacement v‖ ≤ R ∧
        ‖physicalPeriodicGapDisplacement v‖ ≤ R ∧
        ∀ M : ℕ, N ≤ M →
          ‖physicalPeriodicMidpointDisplacement v -
            Coeff.truncate (Finset.Icc (-(M : ℤ)) M) (physicalPeriodicMidpointDisplacement v)‖ ≤ ε ∧
          ‖physicalPeriodicGapDisplacement v -
            Coeff.truncate (Finset.Icc (-(M : ℤ)) M) (physicalPeriodicGapDisplacement v)‖ ≤ ε := by
  obtain ⟨N,hN,U,ho,hu,R,hR,h⟩ :=
    sourceCorollary1_3 (by simp) (by norm_num) (sourcePhysicalL2Equiv.symm u) hε
  refine ⟨N,hN,sourcePhysicalL2Equiv.symm ⁻¹' U,
    ho.preimage sourcePhysicalL2Equiv.symm.continuous,hu,R,hR,?_⟩
  intro v hv
  simpa only [physicalPeriodicMidpointDisplacement_eq_source,
    physicalPeriodicGapDisplacement_eq_source] using h (sourcePhysicalL2Equiv.symm v) hv

/-- A collapsed physical gap is exactly an equal pair of endpoints. -/
theorem physicalPeriodicGap_eq_zero_iff (u : IntervalPairL2) (n : ℤ) :
    physicalPeriodicGap u n = 0 ↔ physicalPeriodicLeft u n = physicalPeriodicRight u n := by
  exact sub_eq_zero.trans eq_comm

end NLS.ZakharovShabat
