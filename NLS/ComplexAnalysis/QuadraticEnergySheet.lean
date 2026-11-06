import NLS.ComplexAnalysis.PrincipalSquareRootSheet
import NLS.ComplexAnalysis.DenseNonreal

/-! The right frequency half-plane fixes the actual principal quadratic
energy sheet. Nonreal energies are dense, so continuous sheet identities
there determine their real-band extensions. -/
noncomputable section
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem sq_mem_slitPlane_of_re_pos (z : ℂ) (hz : 0 < z.re) : z^2 ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases hi : z.im = 0
  · left
    simp only [pow_two,mul_re,hi,mul_zero,sub_zero]
    positivity
  · right
    simp only [pow_two,mul_im]
    have hp := mul_ne_zero hz.ne' hi
    intro he
    apply hp
    linear_combination he/2

theorem sqrt_sq_of_re_pos (z : ℂ) (hz : 0 < z.re) : Complex.sqrt (z^2) = z :=
  (eq_principalSqrt_of_sq_of_re_pos z (z^2) rfl hz).symm

theorem quadraticEnergyMap_injOn_right (c : ℂ) :
    InjOn (fun z : ℂ => z^2-c) {z : ℂ | 0 < z.re} := by
  intro z hz w hw he
  change 0 < z.re at hz
  change 0 < w.re at hw
  have hs : z^2 = w^2 := by
    have h := congrArg (fun v : ℂ => v+c) he
    simpa only [sub_add_cancel] using h
  rcases eq_or_eq_neg_of_sq_eq_sq z w hs with h | h
  · exact h
  · have hr := congrArg Complex.re h
    simp only [neg_re] at hr
    linarith

end NLS.ComplexAnalysis
