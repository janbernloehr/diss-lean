import NLS.ZakharovShabat.SourceDirichletSpectralGlobalExistence

/-! # The actual complete Hilbert spectral flow

The globally constructed integral curve is unique among actual solutions
with the same initial source. Time translation therefore gives the flow
addition law and inverse-time law on the original real source form.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Complex Filter Topology NLS.Poisson NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- The actual global real curve is the unique global actual solution
with its initial source, even among complex source-space solutions. -/
theorem sourceDirichletSpectralGlobalCurve_eq_of_integralCurve
    (k : ℤ) (φ : realTypeSourceLocus 2) (η : ℝ → CoeffPair 2)
    (hη0 : η 0 = φ.val)
    (hη : ∀ t : ℝ, HasDerivAt η
      (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (η t)) t) :
    sourceDirichletSpectralGlobalCurve k φ = η := by
  have heq : EqOn (sourceDirichletSpectralGlobalCurve k φ) η univ := by
    apply eqOn_integralCurves_of_contDiffAt _ _ η univ isOpen_univ isPreconnected_univ
      (fun t _ => hasDerivAt_sourceDirichletSpectralGlobalCurve k φ t)
      (fun t _ => hη t) _ 0 (mem_univ 0)
      ((sourceDirichletSpectralGlobalCurve_zero k φ).trans hη0.symm)
    intro t _
    exact (analyticAt_sourceDirichletSpectralVector_of_realType
      (by simp) (by norm_num) (by norm_num) k
      ⟨sourceDirichletSpectralGlobalCurve k φ t,sourceDirichletSpectralGlobalCurve_realType k φ t⟩).contDiffAt.restrict_scalars ℝ
  funext t
  exact heq (mem_univ t)

/-- The actual indexed flow takes values in the original real source form. -/
def sourceDirichletSpectralFlow (k : ℤ) (φ : realTypeSourceLocus 2) (t : ℝ) : realTypeSourceLocus 2 :=
  ⟨sourceDirichletSpectralGlobalCurve k φ t,sourceDirichletSpectralGlobalCurve_realType k φ t⟩

@[simp] theorem sourceDirichletSpectralFlow_zero (k : ℤ) (φ : realTypeSourceLocus 2) :
    sourceDirichletSpectralFlow k φ 0 = φ :=
  Subtype.ext (sourceDirichletSpectralGlobalCurve_zero k φ)

/-- The original coefficient-space values of the flow solve the actual
indexed ODE at every real time. -/
theorem hasDerivAt_sourceDirichletSpectralFlow_val
    (k : ℤ) (φ : realTypeSourceLocus 2) (t : ℝ) :
    HasDerivAt (fun τ => (sourceDirichletSpectralFlow k φ τ).val)
      (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k
        (sourceDirichletSpectralFlow k φ t).val) t :=
  hasDerivAt_sourceDirichletSpectralGlobalCurve k φ t

/-- Time translation is another actual integral curve. Uniqueness
identifies it with the global curve through its translated initial source. -/
theorem sourceDirichletSpectralFlow_add (k : ℤ) (φ : realTypeSourceLocus 2) (s t : ℝ) :
    sourceDirichletSpectralFlow k (sourceDirichletSpectralFlow k φ s) t =
      sourceDirichletSpectralFlow k φ (s+t) := by
  let η : ℝ → CoeffPair 2 := fun τ => sourceDirichletSpectralGlobalCurve k φ (s+τ)
  have hη0 : η 0 = (sourceDirichletSpectralFlow k φ s).val := by simp [η,sourceDirichletSpectralFlow]
  have hη (τ : ℝ) : HasDerivAt η
      (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (η τ)) τ := by
    have hshift : HasDerivAt (fun u : ℝ => s+u) 1 τ := by
      simpa only [id_eq] using (hasDerivAt_id τ).const_add s
    have h := HasDerivAt.scomp (h := fun u : ℝ => s+u) τ
      (hasDerivAt_sourceDirichletSpectralGlobalCurve k φ (s+τ)) hshift
    simpa only [Function.comp_def,one_smul] using h
  apply Subtype.ext
  exact congrFun (sourceDirichletSpectralGlobalCurve_eq_of_integralCurve
    k (sourceDirichletSpectralFlow k φ s) η hη0 hη) t

/-- Negative time is the inverse of positive time for the actual flow. -/
@[simp] theorem sourceDirichletSpectralFlow_neg (k : ℤ) (φ : realTypeSourceLocus 2) (t : ℝ) :
    sourceDirichletSpectralFlow k (sourceDirichletSpectralFlow k φ t) (-t) = φ := by
  rw [sourceDirichletSpectralFlow_add]
  simp

/-- The complete actual flow preserves the original source norm and
all actual discriminants for every real time. -/
theorem sourceDirichletSpectralFlow_conserved (k : ℤ) (φ : realTypeSourceLocus 2) (t : ℝ) :
    ‖(sourceDirichletSpectralFlow k φ t).val‖ = ‖φ.val‖ ∧ ∀ w : ℂ,
      canonicalDiscriminant (by simp) (periodOnePotential (sourceDirichletSpectralFlow k φ t).val) w =
        canonicalDiscriminant (by simp) (periodOnePotential φ.val) w :=
  sourceDirichletSpectralGlobalCurve_conserved k φ t

/-- Any actual local solution through the initial source agrees with
the complete flow throughout its original open interval. The supplied
solution need not be assumed real. -/
theorem sourceDirichletSpectralFlow_eqOn_integralCurve
    (k : ℤ) (φ : realTypeSourceLocus 2) (η : ℝ → CoeffPair 2) (a b : ℝ)
    (h0 : (0 : ℝ) ∈ Ioo a b) (hη0 : η 0 = φ.val)
    (hη : ∀ t ∈ Ioo a b, HasDerivAt η
      (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (η t)) t) :
    EqOn (fun t => (sourceDirichletSpectralFlow k φ t).val) η (Ioo a b) := by
  apply eqOn_integralCurves_of_contDiffAt _ _ η (Ioo a b) isOpen_Ioo
    (convex_Ioo a b).isPreconnected
    (fun t _ => hasDerivAt_sourceDirichletSpectralFlow_val k φ t) hη _ 0 h0
    ((sourceDirichletSpectralGlobalCurve_zero k φ).trans hη0.symm)
  intro t _
  exact (analyticAt_sourceDirichletSpectralVector_of_realType
    (by simp) (by norm_num) (by norm_num) k (sourceDirichletSpectralFlow k φ t)).contDiffAt.restrict_scalars ℝ

/-- Every actual periodic gap is fixed for all real times, including
collapsed gaps and gaps other than the selected flow index. -/
theorem canonicalPeriodicGap_sourceDirichletSpectralFlow
    (k j : ℤ) (φ : realTypeSourceLocus 2) (t : ℝ) :
    canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (sourceDirichletSpectralFlow k φ t).val)
      (periodOnePotential_mem (sourceDirichletSpectralFlow k φ t).val) j =
    canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) j := by
  let γ := sourceDirichletSpectralGlobalCurve k φ
  change canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential (γ t)) (periodOnePotential_mem (γ t)) j =
    canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential φ.val) (periodOnePotential_mem φ.val) j
  have hzero : γ 0 = φ.val := sourceDirichletSpectralGlobalCurve_zero k φ
  let a : ℝ := min t 0-1
  let b : ℝ := max t 0+1
  have ht : t ∈ Ioo a b := ⟨by dsimp [a]; linarith [min_le_left t 0],
    by dsimp [b]; linarith [le_max_left t 0]⟩
  have h0 : (0 : ℝ) ∈ Ioo a b := ⟨by dsimp [a]; linarith [min_le_right t 0],
    by dsimp [b]; linarith [le_max_right t 0]⟩
  simpa only [hzero] using canonicalPeriodicGap_eq_on_sourceDirichletSpectral_integralCurve
    (by simp) (by norm_num) (by norm_num) k j γ a b
    (fun s _ => sourceDirichletSpectralGlobalCurve_realType k φ s)
    (fun s _ => hasDerivAt_sourceDirichletSpectralGlobalCurve k φ s) t 0 ht h0

end NLS.ZakharovShabat
