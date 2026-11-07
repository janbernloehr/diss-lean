import NLS.KdV.HillProductColumnMeanValue
import NLS.KdV.HillIndependentPsiPullback
import NLS.ZakharovShabat.SourcePsiGapFactorization

/-! Filled algebra for Hill product columns. No selected-root divisor
is introduced: the frequency factorization holds even at collisions. -/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal Classical
namespace NLS.KdV

theorem hillEnergyProductCoordinateDerivative_cross (n m r : ℕ+) (hmn : m ≠ n) (hrn : r ≠ n)
    (E : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    (m:ℕ)*(hillEnergySequenceZero r d-E)*hillEnergyProductCoordinateDerivative n r (E,d) =
      (r:ℕ)*(hillEnergySequenceZero m d-E)*hillEnergyProductCoordinateDerivative n m (E,d) := by
  have hm := hillEnergyProductCoordinateDerivative_restore n m hmn E d
  have hr := hillEnergyProductCoordinateDerivative_restore n r hrn E d
  linear_combination (m:ℕ)*hr-(r:ℕ)*hm

theorem hillEnergyProductCoordinateDerivative_frequency_filled (n m : ℕ+) (hmn : m ≠ n)
    (c : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2) (z : ℂ) :
    (hillIndependentFrequency (c,d) ((n:ℕ):ℤ)-z)*
      (hillIndependentFrequency (c,d) ((n:ℕ):ℤ)+z)*
      (hillIndependentFrequency (c,d) ((m:ℕ):ℤ)+z)*z*
      hillEnergyProductCoordinateDerivative n m (z^2-c,d) =
      -((Real.pi:ℂ)*(n:ℕ))^2*(m:ℕ)*jointDeletedSingleSpectralProduct ((m:ℕ):ℤ)
        (z,hillIndependentFrequencyDisplacement (c,d)) := by
  let a := hillIndependentFrequencyDisplacement (c,d)
  let bn := hillIndependentFrequency (c,d) ((n:ℕ):ℤ)
  let bm := hillIndependentFrequency (c,d) ((m:ℕ):ℤ)
  let A : ℂ := ((Real.pi:ℂ)*(n:ℕ))^2
  let f : ℂ → ℂ := fun w => (bn-w)*(bn+w)*(bm+w)*w*hillEnergyProductCoordinateDerivative n m (w^2-c,d)
  let g : ℂ → ℂ := fun w => -A*(m:ℕ)*jointDeletedSingleSpectralProduct ((m:ℕ):ℤ) (w,a)
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro w
    exact (analyticAt_const.sub analyticAt_id |>.mul (analyticAt_const.add analyticAt_id) |>.mul
      (analyticAt_const.add analyticAt_id) |>.mul analyticAt_id |>.mul
      ((analyticAt_hillEnergyProductCoordinateDerivative n m _).comp
        (((analyticAt_id.pow 2).sub analyticAt_const).prod analyticAt_const))).continuousAt
  have hg : Continuous g := by
    have hc : Continuous (fun w : ℂ => sourcePsiCandidate ((m:ℕ):ℤ) (w,a)) :=
      (continuousOn_univ.mp (analyticOnNhd_sourcePsiCandidate (by norm_num) (by norm_num) ((m:ℕ):ℤ)).continuousOn).comp
        (continuous_id.prodMk continuous_const)
    have he : g = fun w => (A*(m:ℕ)/2)*sourcePsiCandidate ((m:ℕ):ℤ) (w,a) := by
      funext w
      simp only [g,sourcePsiCandidate]
      ring
    rw [he]
    exact continuous_const.mul hc
  have he : f = g := by
    apply Continuous.ext_on ((Set.to_countable {bm}).dense_compl ℂ) hf hg
    intro w hw
    have hbm : bm-w ≠ 0 := sub_ne_zero.mpr (Ne.symm (by simpa only [mem_compl_iff,mem_singleton_iff] using hw))
    apply mul_left_cancel₀ hbm
    have h1 := hillEnergyProduct_independent_candidate_filled n c d w
    have h2 := sourcePsiCandidate_change_deleted_index (by norm_num) (by norm_num)
      ((n:ℕ):ℤ) ((m:ℕ):ℤ) a w
    have h3 := hillEnergyProductCoordinateDerivative_restore n m hmn (w^2-c) d
    have hs : hillEnergySequenceZero m d-(w^2-c) = bm^2-w^2 := by
      rw [hillIndependentFrequency_positive_sq (c,d) m]
      ring
    rw [hs] at h3
    change (bn+w)*(2*w*hillEnergySequenceProduct n (w^2-c,d)) = A*sourcePsiCandidate ((n:ℕ):ℤ) (w,a) at h1
    change (bn-w)*sourcePsiCandidate ((n:ℕ):ℤ) (w,a) =
      (bm-w)*(-2*jointDeletedSingleSpectralProduct ((m:ℕ):ℤ) (w,a)) at h2
    dsimp only [f,g]
    linear_combination (bn-w)*(bn+w)*w*h3+((m:ℕ):ℂ)/2*(bn-w)*h1+A*((m:ℕ):ℂ)/2*h2
  exact congrFun he z

end NLS.KdV
