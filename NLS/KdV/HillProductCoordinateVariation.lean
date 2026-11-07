import NLS.KdV.HillProductCoordinateCutoffs

/-! The full literal Hill product is affine in each zero coordinate.
Its filled coordinate derivative is jointly entire, including at zero
factors. Division-free restoration gives every retained complex root. -/
noncomputable section
open Set Complex Filter Topology
open scoped ENNReal Classical
namespace NLS.KdV

def hillEnergyProductCoordinateDerivative (n m : ℕ+)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : ℂ :=
  hillEnergySequenceProduct n (t.1,hillZeroCoordinateShift m t.2 1)-hillEnergySequenceProduct n t

theorem hillEnergySequenceProduct_coordinate_affine (n m : ℕ+) (E : ℂ)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (z : ℂ) :
    hillEnergySequenceProduct n (E,hillZeroCoordinateShift m d z) =
      hillEnergySequenceProduct n (E,d)+z*hillEnergyProductCoordinateDerivative n m (E,d) := by
  have hbase := tendsto_hillEnergySequencePartialProduct n (E,d)
  have hshift := tendsto_hillEnergySequencePartialProduct n (E,hillZeroCoordinateShift m d 1)
  have hlim := hbase.add ((hshift.sub hbase).const_mul z)
  exact tendsto_nhds_unique (tendsto_hillEnergySequencePartialProduct n (E,hillZeroCoordinateShift m d z))
    (hlim.congr' (Eventually.of_forall (fun N =>
      (hillEnergySequencePartialProduct_coordinate_affine n m N E d z).symm)))

theorem hillEnergySequenceProduct_omitted_shift (n : ℕ+) (E : ℂ)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (z : ℂ) :
    hillEnergySequenceProduct n (E,hillZeroCoordinateShift n d z) = hillEnergySequenceProduct n (E,d) := by
  have h := tendsto_hillEnergySequencePartialProduct n (E,hillZeroCoordinateShift n d z)
  simp_rw [hillEnergySequencePartialProduct_omitted_shift] at h
  exact tendsto_nhds_unique h (tendsto_hillEnergySequencePartialProduct n (E,d))

theorem hillEnergyProductCoordinateDerivative_omitted (n : ℕ+)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : hillEnergyProductCoordinateDerivative n n t = 0 := by
  rw [hillEnergyProductCoordinateDerivative,hillEnergySequenceProduct_omitted_shift,sub_self]

theorem analyticAt_hillEnergyProductCoordinateDerivative (n m : ℕ+)
    (t : ℂ × lp (fun _ : ℕ+ => ℂ) 2) : AnalyticAt ℂ (hillEnergyProductCoordinateDerivative n m) t := by
  have hs : AnalyticAt ℂ (fun s : ℂ × lp (fun _ : ℕ+ => ℂ) 2 =>
      (s.1,hillZeroCoordinateShift m s.2 1)) t :=
    analyticAt_fst.prod (analyticAt_snd.add analyticAt_const)
  exact ((analyticAt_hillEnergySequenceProduct n _).comp
    (f := fun s : ℂ × lp (fun _ : ℕ+ => ℂ) 2 => (s.1,hillZeroCoordinateShift m s.2 1)) hs).sub
      (analyticAt_hillEnergySequenceProduct n t)

theorem hasDerivAt_hillEnergySequenceProduct_coordinate (n m : ℕ+) (E : ℂ)
    (d : lp (fun _ : ℕ+ => ℂ) 2) (z : ℂ) :
    HasDerivAt (fun w : ℂ => hillEnergySequenceProduct n (E,hillZeroCoordinateShift m d w))
      (hillEnergyProductCoordinateDerivative n m (E,d)) z := by
  have he : (fun w : ℂ => hillEnergySequenceProduct n (E,hillZeroCoordinateShift m d w)) =
      (fun w : ℂ => hillEnergySequenceProduct n (E,d)+w*hillEnergyProductCoordinateDerivative n m (E,d)) :=
    funext (hillEnergySequenceProduct_coordinate_affine n m E d)
  rw [he]
  simpa only [zero_add,one_mul,id_eq] using! (hasDerivAt_const z (hillEnergySequenceProduct n (E,d))).add
    ((hasDerivAt_id z).mul_const (hillEnergyProductCoordinateDerivative n m (E,d)))

theorem hillEnergyProductCoordinateDerivative_restore (n m : ℕ+) (hmn : m ≠ n)
    (E : ℂ) (d : lp (fun _ : ℕ+ => ℂ) 2) :
    (hillEnergySequenceZero m d-E)*hillEnergyProductCoordinateDerivative n m (E,d) =
      (m:ℕ)*hillEnergySequenceProduct n (E,d) := by
  have hbase := tendsto_hillEnergySequencePartialProduct n (E,d)
  have hshift := tendsto_hillEnergySequencePartialProduct n (E,hillZeroCoordinateShift m d 1)
  have hL := (hshift.sub hbase).const_mul (hillEnergySequenceZero m d-E)
  have hR := hbase.const_mul ((m:ℕ):ℂ)
  have he : ∀ᶠ N : ℕ in atTop,
      (hillEnergySequenceZero m d-E)*(hillEnergySequencePartialProduct n N (E,hillZeroCoordinateShift m d 1)-
        hillEnergySequencePartialProduct n N (E,d)) = (m:ℕ)*hillEnergySequencePartialProduct n N (E,d) := by
    filter_upwards [eventually_ge_atTop (m:ℕ)] with N hN
    exact hillEnergySequencePartialProduct_coordinate_restore n m hmn N hN E d
  exact tendsto_nhds_unique (hL.congr' he) hR

theorem hillEnergySequenceProduct_retained_root (n m : ℕ+) (hmn : m ≠ n)
    (d : lp (fun _ : ℕ+ => ℂ) 2) : hillEnergySequenceProduct n (hillEnergySequenceZero m d,d) = 0 := by
  have h := hillEnergyProductCoordinateDerivative_restore n m hmn (hillEnergySequenceZero m d) d
  rw [sub_self,zero_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_left (by exact_mod_cast m.ne_zero)

end NLS.KdV
