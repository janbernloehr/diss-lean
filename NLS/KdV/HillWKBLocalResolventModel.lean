import NLS.KdV.HillWKBDirichletComparison

/-! # The bounded local Riccati resolvent factor of the actual WKB model -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ContDiff
namespace NLS.KdV

def hillWKBLocalResolvent (f : ℝ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  let r := nlsRiccatiApproximation (fun _ => -1) (-f) N (2*I*z)⁻¹ 0
  let s := nlsRiccatiApproximation f (fun _ => 1) N (2*I*(-z))⁻¹ 0
  (-s/(1+r*s))

theorem hillWKBDirichletModel_eq_localResolvent_mul (f : ℝ → ℂ) (N : ℕ) (z : ℂ) :
    hillWKBDirichletModel f N z=hillWKBLocalResolvent f N z*
      (exp (nlsHamiltonianPhase (fun _ => -1) (-f) N z)-
        (exp (nlsHamiltonianPhase (fun _ => -1) (-f) N z))⁻¹) := by
  unfold hillWKBDirichletModel hillWKBLocalResolvent
  ring

theorem exists_hillWKBLocalResolvent_bound (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (N : ℕ) :
    ∃ R : ℝ, 1≤R ∧ ∀ z : ℂ, R≤‖z‖ → ‖hillWKBLocalResolvent f N z‖≤1 := by
  obtain ⟨R,hR,hbasis⟩ := exists_nlsWKB_initial_basis_small (fun _ => -1) (-f) contDiff_const hf.neg N
  refine ⟨R,hR,?_⟩
  intro z hz
  let r := nlsRiccatiApproximation (fun _ => -1) (-f) N (2*I*z)⁻¹ 0
  let s := nlsRiccatiApproximation f (fun _ => 1) N (2*I*(-z))⁻¹ 0
  obtain ⟨_hℓ,hu,_hd,hi⟩ := hbasis z hz
  have hf' : -(-f)=f := neg_neg f
  have hone : (-(fun _ : ℝ => (-1:ℂ)))=(fun _ => (1:ℂ)) := by funext x;norm_num
  rw [hf',hone] at hu hi
  change ‖-I*s‖≤1/2 at hu
  change ‖(1-(-I*r)*(-I*s))⁻¹‖≤2 at hi
  have hden : 1-(-I*r)*(-I*s)=1+r*s := by ring_nf;simp only [I_sq];ring
  rw [hden] at hi
  have hs : ‖s‖≤1/2 := by simpa only [norm_mul,norm_neg,norm_I,one_mul] using hu
  change ‖-s/(1+r*s)‖≤1
  rw [div_eq_mul_inv,norm_mul,norm_neg]
  exact (mul_le_mul hs hi (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

end NLS.KdV
