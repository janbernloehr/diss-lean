import NLS.SequenceSpaces.SpectralWeightInterpolation
import Mathlib.Topology.LocallyFinite

/-! # Continuity of the exact piecewise-linear spectral weight -/
noncomputable section
open Set Filter Topology
namespace NLS.SpectralWeight

/-- The closed unit intervals form a locally finite cover of the nonnegative line. -/
private theorem locallyFinite_nat_unit_intervals :
    LocallyFinite (fun n : ℕ => Icc (n:ℝ) ((n:ℝ)+1)) := by
  intro x
  refine ⟨Iio (x+1),Iio_mem_nhds (by linarith),?_⟩
  apply (Set.finite_Iic ⌈x+1⌉₊).subset
  rintro n ⟨y,hy,hyx⟩
  have hn : (n:ℝ) ≤ (⌈x+1⌉₊:ℝ) := le_trans (hy.1.trans hyx.le) (Nat.le_ceil _)
  exact_mod_cast hn

/-- Linear interpolation is continuous even at integral arguments and at zero. -/
theorem continuous_realExtension (w : SpectralWeight) : Continuous w.realExtension := by
  have hcover : (⋃ n : ℕ, Icc (n:ℝ) ((n:ℝ)+1)) = Ici (0:ℝ) := by
    ext t
    constructor
    · intro ht
      obtain ⟨n,hn⟩ := mem_iUnion.mp ht
      exact (Nat.cast_nonneg n).trans hn.1
    · intro ht
      exact mem_iUnion.mpr ⟨⌊t⌋₊,Nat.floor_le ht,(Nat.lt_floor_add_one t).le⟩
  have hcont (n : ℕ) : ContinuousOn w.realExtension (Icc (n:ℝ) ((n:ℝ)+1)) := by
    have h := (show Continuous (fun t : ℝ =>
      (1-(t-n))*w n+(t-n)*w ((n:ℤ)+1)) by fun_prop)
    apply h.continuousOn.congr
    intro t ht
    have he := w.realExtension_affine n (t-n) (by linarith [ht.1]) (by linarith [ht.2])
    simpa only [add_sub_cancel] using he
  have hpos := locallyFinite_nat_unit_intervals.continuousOn_iUnion (fun _ => isClosed_Icc) hcont
  rw [hcover] at hpos
  have he (t : ℝ) : w.realExtension |t| = w.realExtension t := by simp [realExtension]
  exact (hpos.comp_continuous continuous_abs (fun t => abs_nonneg t)).congr he

end NLS.SpectralWeight
