import NLS.KdV.HillIndependentPsiPullback
import NLS.ZakharovShabat.SourcePsiOriginalCoordinateBound

/-! The EXACT extra Hill-to-Dirac contour multiplier is uniformly
bounded before ALL positive row and numerator indices on the original
isolating discs, for independently placed BALANCED frequency roots.
The source's original separation constant is retained. -/
noncomputable section
open Set Complex NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillIndependent_multiplier_bound
    {V : Set (CoeffPair 2)} {D : ℤ → Set ℂ} {C : ℝ}
    (hD : SourceIsolatingNeighborhoods (by norm_num) (by norm_num) V D C)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2)
    (hplace : ∀ k : ℤ, hillIndependentFrequency t k ∈ D k)
    (n m : ℕ+) (z : ℂ) (hz : z ∈ closure (D ((m:ℕ):ℤ))) :
    hillIndependentFrequency t ((n:ℕ):ℤ)+z ≠ 0 ∧
      ‖(Real.pi:ℂ)^2*(((n:ℕ):ℂ)+((m:ℕ):ℂ))/(hillIndependentFrequency t ((n:ℕ):ℤ)+z)‖ ≤
        Real.pi^2*C := by
  have hmn : ((m:ℕ):ℤ) ≠ -((n:ℕ):ℤ) := by
    have hm : 0 < ((m:ℕ):ℤ) := by exact_mod_cast m.pos
    have hn : 0 < ((n:ℕ):ℤ) := by exact_mod_cast n.pos
    omega
  have hneg : -hillIndependentFrequency t ((n:ℕ):ℤ) ∈ D (-((n:ℕ):ℤ)) := by
    rw [← hillIndependentFrequency_neg]
    exact hplace _
  have hs := hD.weighted_separation_closure (-((n:ℕ):ℤ)) ((m:ℕ):ℤ) hmn
    (-hillIndependentFrequency t ((n:ℕ):ℤ)) hneg z hz
  have hne : hillIndependentFrequency t ((n:ℕ):ℤ)+z ≠ 0 := by
    intro h
    apply hs.1
    linear_combination h
  refine ⟨hne,?_⟩
  have hb := hs.2
  have hnum : ((-((n:ℕ):ℤ)-((m:ℕ):ℤ):ℤ):ℂ) = -(((n:ℕ):ℂ)+((m:ℕ):ℂ)) := by
    push_cast
    ring
  rw [hnum,norm_neg,show -hillIndependentFrequency t ((n:ℕ):ℤ)-z =
    -(hillIndependentFrequency t ((n:ℕ):ℤ)+z) by ring,norm_neg] at hb
  rw [norm_div,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le,mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hb (sq_nonneg Real.pi)

end NLS.KdV
