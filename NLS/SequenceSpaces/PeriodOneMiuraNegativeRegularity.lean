import NLS.SequenceSpaces.PeriodOneMiuraFiniteRegularity
import NLS.SequenceSpaces.FractionalMiuraRecovery

/-! The literal distributional Miura image has the exact negative
Hilbert regularity forced by a positive fractional lift. -/
noncomputable section
open Complex NLS.WeightedCoeff
open scoped ENNReal
namespace NLS

theorem periodOneMiura_memlp_negative_of_lift (r : ℝ) (hr : 0 ≤ r) (hr1 : r < 1)
    (u : Coeff 2) (hu : Memℓp (fun k => (Weight.sobolev (1-r) k:ℂ)*u k) 2) :
    Memℓp (fun k => (Weight.sobolev (-r) k:ℂ)*(periodOneMiura u).val k) 2 := by
  by_cases hrhalf : 1/2 < r
  · exact (periodOneMiura_memlp_iff r (by norm_num) le_rfl (by norm_num; linarith) u).mpr hu
  · let U : WeightedCoeff (Weight.sobolev (1-r)) 2 := ⟨u,hu⟩
    let U₃ := sobolevInclusion (show (1/3:ℝ) ≤ 1-r by linarith) U
    have hraw₃ (k : ℤ) : U₃.val k = u k := sobolevInclusion_apply _ U k
    let Y := l2ToNegativeSobolev r hr (miuraThirdL2Product U₃)
    have hY : Memℓp (fun k => (Weight.sobolev (-r) k:ℂ)*
        (∑' j : ℤ, u (k-j)*u j)) 2 := by
      have h := Y.property
      change Memℓp (fun k => (Weight.sobolev (-r) k:ℂ)*Y.val k) 2 at h
      convert h using 1
      funext k
      dsimp only [Y]
      rw [l2ToNegativeSobolev_apply,miuraThirdL2Product_apply]
      simp only [hraw₃]
    let A : WeightedCoeff (Weight.sobolev (-r+1)) 2 := ⟨u,by
      change Memℓp (fun k => (Weight.sobolev (-r+1) k:ℂ)*u k) 2
      simpa only [show -r+1 = 1-r by ring] using hu⟩
    have hd := (sobolevDerivative (-r) A).property
    change Memℓp (fun k => (Weight.sobolev (-r) k:ℂ)*
      (sobolevDerivative (-r) A).val k) 2 at hd
    have hh := (hd.const_mul (2:ℂ)).add hY
    have heq : (fun k : ℤ => (Weight.sobolev (-r) k:ℂ)*(periodOneMiura u).val k) =
        (fun k => (2:ℂ)*((Weight.sobolev (-r) k:ℂ)*(sobolevDerivative (-r) A).val k))+
          (fun k => (Weight.sobolev (-r) k:ℂ)*(∑' j : ℤ, u (k-j)*u j)) := by
      funext k
      simp only [Pi.add_apply]
      rw [periodOneMiura_apply,sobolevDerivative_apply]
      change (Weight.sobolev (-r) k:ℂ)*(2*I*(Real.pi:ℂ)*k*u k+
        (∑' j : ℤ, u (k-j)*u j)) =
        2*((Weight.sobolev (-r) k:ℂ)*(I*(Real.pi:ℂ)*k*u k))+
          (Weight.sobolev (-r) k:ℂ)*(∑' j : ℤ, u (k-j)*u j)
      ring
    rw [heq]
    exact hh

end NLS
