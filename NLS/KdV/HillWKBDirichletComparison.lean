import NLS.ZakharovShabat.NLSWKBTwoColumnComparison
import NLS.KdV.HillL2DirichletCharacteristic

/-! # Actual scalar Hill Dirichlet characteristic from both WKB columns -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.KdV

theorem classicalHillDirichlet_eq_monodromy_entry (q : Curve ℂ) (z : ℂ) :
    (classicalHillFlow q (z^2) (0,1) 1).1=
      I*(classicalMonodromy (constantUpperPotential q) z) 0 1 := by
  rw [classicalHillFlow_eq_constantUpper q z (0,1) ⟨1,by norm_num⟩]
  simp only [constantUpperStateMap_apply,constantUpperInitialVector,mul_one,mul_zero,sub_zero]
  change (classicalSolution (constantUpperPotential q) z (0,I) 1).1=
    I*(classicalSolution (constantUpperPotential q) z (0,1) 1).1
  rw [classicalSolution_eq_columns _ _ _ ⟨1,by norm_num⟩]
  simp

def hillWKBDirichletModel (f : ℝ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  let r := nlsRiccatiApproximation (fun _ => -1) (-f) N (2*I*z)⁻¹ 0
  let s := nlsRiccatiApproximation f (fun _ => 1) N (2*I*(-z))⁻¹ 0
  let m := exp (nlsHamiltonianPhase (fun _ => -1) (-f) N z)
  (-s*(m-m⁻¹)/(1+r*s))

theorem exists_hillL2Dirichlet_wkb_error_bound
    (Q : C(AddCircle (2:ℝ),ℂ))
    (hf : ContDiff ℝ ∞ (fun x : ℝ => Q (x : AddCircle (2:ℝ))))
    (hp : Function.Periodic (fun x : ℝ => Q (x : AddCircle (2:ℝ))) 1) (N : ℕ) :
    ∃ R C : ℝ, 1≤R ∧ 0<C ∧ ∀ z : ℂ, R≤‖z‖ →
      ‖hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)) (z^2)-
        hillWKBDirichletModel (fun x : ℝ => Q (x : AddCircle (2:ℝ))) N z‖≤
          C/(2*‖z‖)^N*Real.exp |z.im| := by
  let f : ℝ → ℂ := fun x => Q (x : AddCircle (2:ℝ))
  obtain ⟨R,C,hR,hC,hbound⟩ := exists_classicalMonodromy_upper_right_wkb_error_bound
    (fun _ => -1) (-f) contDiff_const hf.neg (fun _ => rfl) (fun x => congrArg Neg.neg (hp x)) N
  refine ⟨R,C,hR,hC,?_⟩
  intro z hz
  have h := hbound z hz
  dsimp only at h
  let r := nlsRiccatiApproximation (fun _ => -1) (-f) N (2*I*z)⁻¹ 0
  let s := nlsRiccatiApproximation f (fun _ => 1) N (2*I*(-z))⁻¹ 0
  let m := exp (nlsHamiltonianPhase (fun _ => -1) (-f) N z)
  have hpot : constantUpperPotential (hillUnitPotentialCurve Q)=
      classicalPotentialOfFunctions (fun _ => -1) (-f) continuous_const hf.neg.continuous := by
    apply ContinuousMap.ext
    intro t
    apply Prod.ext
    · rfl
    · simp only [constantUpperPotential_apply,classicalPotentialOfFunctions_apply,Pi.neg_apply]
      congr 1
  rw [hillL2DirichletCharacteristic_eq_classical,classicalHillDirichlet_eq_monodromy_entry,hpot]
  have hu : nlsRiccatiApproximation (-(-f)) (-(fun _ : ℝ => (-1:ℂ))) N (2*I*(-z))⁻¹ 0=s := by
    simp only [neg_neg]
    have he : (-(fun _ : ℝ => (-1:ℂ)))=(fun _ => (1:ℂ)) := by funext x;norm_num
    rw [he]
  rw [hu] at h
  change ‖(classicalMonodromy _ z) 0 1-(-I*s)*(m⁻¹-m)/(1-(-I*r)*(-I*s))‖≤_ at h
  have he : I*((classicalMonodromy (classicalPotentialOfFunctions (fun _ => -1) (-f) continuous_const hf.neg.continuous) z) 0 1-
      (-I*s)*(m⁻¹-m)/(1-(-I*r)*(-I*s)))=
    I*(classicalMonodromy (classicalPotentialOfFunctions (fun _ => -1) (-f) continuous_const hf.neg.continuous) z) 0 1-
      hillWKBDirichletModel f N z := by
    have hd : 1-(-I*r)*(-I*s)=1+r*s := by ring_nf;simp only [I_sq];ring
    rw [hd]
    dsimp only [hillWKBDirichletModel]
    change I*(_-(-I*s)*(m⁻¹-m)/(1+r*s))=_- -s*(m-m⁻¹)/(1+r*s)
    simp only [div_eq_mul_inv]
    ring_nf
    simp only [I_sq]
    ring
  have hn := congrArg norm he
  rw [norm_mul,norm_I,one_mul] at hn
  exact hn ▸ h

end NLS.KdV
