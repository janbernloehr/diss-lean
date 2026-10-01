import NLS.ZakharovShabat.SourceDirichletSpectralUniqueness
import NLS.ZakharovShabat.SourceDirichletSpectralContinuation

/-! # Compatible actual Hilbert spectral trajectories

The time domain is the union of every actual real trajectory interval
through the initial source. Uniqueness makes their values compatible.
Choosing any available trajectory therefore defines one actual curve on
that open interval, independently of which representative was chosen.
-/

noncomputable section
set_option maxHeartbeats 800000
open Set Metric Complex Filter Topology NLS.Poisson
open scoped ENNReal
namespace NLS.ZakharovShabat
local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- An actual real Hilbert spectral trajectory through a fixed source
at time zero, on a nonempty open interval containing zero. -/
structure SourceDirichletSpectralTrajectory (k : ℤ) (φ : realTypeSourceLocus 2) where
  curve : ℝ → CoeffPair 2
  lower : ℝ
  upper : ℝ
  initialTime_mem : (0 : ℝ) ∈ Ioo lower upper
  initialSource : curve 0 = φ.val
  realType : ∀ t ∈ Ioo lower upper, IsRealType (CoeffPair.toMax 2 (curve t))
  hasDerivAt : ∀ t ∈ Ioo lower upper, HasDerivAt curve
    (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k (curve t)) t

/-- Local existence supplies an actual trajectory through every real
Hilbert source, including zero and collapsed-gap sources. -/
theorem nonempty_sourceDirichletSpectralTrajectory (k : ℤ) (φ : realTypeSourceLocus 2) :
    Nonempty (SourceDirichletSpectralTrajectory k φ) := by
  obtain ⟨γ,h0,hreal,ε,hε,hder,_,_⟩ :=
    exists_sourceDirichletSpectral_norm_conserved_integralCurve k φ
  exact ⟨⟨γ,-ε,ε,⟨by linarith,hε⟩,h0,fun t _ => hreal t,hder⟩⟩

/-- All times covered by some actual trajectory through the initial source. -/
def sourceDirichletSpectralTimeDomain (k : ℤ) (φ : realTypeSourceLocus 2) : Set ℝ :=
  {t | ∃ T : SourceDirichletSpectralTrajectory k φ, t ∈ Ioo T.lower T.upper}

theorem zero_mem_sourceDirichletSpectralTimeDomain (k : ℤ) (φ : realTypeSourceLocus 2) :
    (0 : ℝ) ∈ sourceDirichletSpectralTimeDomain k φ := by
  obtain ⟨T⟩ := nonempty_sourceDirichletSpectralTrajectory k φ
  exact ⟨T,T.initialTime_mem⟩

theorem isOpen_sourceDirichletSpectralTimeDomain (k : ℤ) (φ : realTypeSourceLocus 2) :
    IsOpen (sourceDirichletSpectralTimeDomain k φ) := by
  rw [isOpen_iff_eventually]
  rintro t ⟨T,ht⟩
  filter_upwards [isOpen_Ioo.eventually_mem ht] with u hu
  exact ⟨T,hu⟩

/-- All constituent intervals contain zero, so their union is one interval. -/
theorem ordConnected_sourceDirichletSpectralTimeDomain (k : ℤ) (φ : realTypeSourceLocus 2) :
    OrdConnected (sourceDirichletSpectralTimeDomain k φ) := by
  constructor
  rintro u ⟨T,hu⟩ v ⟨U,hv⟩ t ht
  by_cases hneg : t < 0
  · exact ⟨T,⟨hu.1.trans_le ht.1,hneg.trans T.initialTime_mem.2⟩⟩
  · exact ⟨U,⟨U.initialTime_mem.1.trans_le (not_lt.mp hneg),ht.2.trans_lt hv.2⟩⟩

/-- Choose any available trajectory value; the initial source is a
temporary value at uncovered times until completeness of the domain is proved. -/
def sourceDirichletSpectralGlobalCurve (k : ℤ) (φ : realTypeSourceLocus 2) (t : ℝ) : CoeffPair 2 := by
  classical
  exact if h : t ∈ sourceDirichletSpectralTimeDomain k φ then h.choose.curve t else φ.val

/-- The chosen curve agrees with every actual trajectory on its entire
interval, by actual source ODE uniqueness. -/
theorem sourceDirichletSpectralGlobalCurve_eqOn_trajectory
    (k : ℤ) (φ : realTypeSourceLocus 2) (T : SourceDirichletSpectralTrajectory k φ) :
    EqOn (sourceDirichletSpectralGlobalCurve k φ) T.curve (Ioo T.lower T.upper) := by
  intro t ht
  have hmem : t ∈ sourceDirichletSpectralTimeDomain k φ := ⟨T,ht⟩
  rw [sourceDirichletSpectralGlobalCurve,dif_pos hmem]
  let U := hmem.choose
  have hU : t ∈ Ioo U.lower U.upper := hmem.choose_spec
  have heq := sourceDirichletSpectral_integralCurves_eqOn_overlap
    (by simp) (by norm_num) (by norm_num) k U.curve T.curve U.lower U.upper T.lower T.upper
    U.realType U.hasDerivAt T.hasDerivAt 0 ⟨U.initialTime_mem,T.initialTime_mem⟩
    (U.initialSource.trans T.initialSource.symm)
  exact heq ⟨hU,ht⟩

@[simp] theorem sourceDirichletSpectralGlobalCurve_zero (k : ℤ) (φ : realTypeSourceLocus 2) :
    sourceDirichletSpectralGlobalCurve k φ 0 = φ.val := by
  obtain ⟨T⟩ := nonempty_sourceDirichletSpectralTrajectory k φ
  exact (sourceDirichletSpectralGlobalCurve_eqOn_trajectory k φ T T.initialTime_mem).trans T.initialSource

theorem sourceDirichletSpectralGlobalCurve_realType (k : ℤ) (φ : realTypeSourceLocus 2) (t : ℝ) :
    IsRealType (CoeffPair.toMax 2 (sourceDirichletSpectralGlobalCurve k φ t)) := by
  unfold sourceDirichletSpectralGlobalCurve
  split_ifs with h
  · exact h.choose.realType t h.choose_spec
  · exact φ.property

/-- Agreement on a neighborhood transfers the actual derivative from
any representative trajectory to the assembled curve. -/
theorem hasDerivAt_sourceDirichletSpectralGlobalCurve_of_mem
    (k : ℤ) (φ : realTypeSourceLocus 2) (t : ℝ)
    (ht : t ∈ sourceDirichletSpectralTimeDomain k φ) :
    HasDerivAt (sourceDirichletSpectralGlobalCurve k φ)
      (sourceDirichletSpectralVector (by simp) (by norm_num) (by norm_num) k
        (sourceDirichletSpectralGlobalCurve k φ t)) t := by
  obtain ⟨T,hT⟩ := ht
  have heq := sourceDirichletSpectralGlobalCurve_eqOn_trajectory k φ T
  rw [heq hT]
  apply (T.hasDerivAt t hT).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.eventually_mem hT] with u hu
  exact heq hu

end NLS.ZakharovShabat
