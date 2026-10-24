import NLS.ZakharovShabat.L2WholeLinePotentialPeriods
import NLS.ZakharovShabat.SourcePhysicalRealL2

/-! # Almost-everywhere reality of the actual periodized physical potential

Almost-everywhere properties of the original unit-interval L2 representative
extend through every integer period. In particular, the real source condition
gives the Hermitian off-diagonal relation on the full real line.
-/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
namespace NLS.ZakharovShabat

/-- A null-set-invariant pointwise property of the original unit-interval
potential holds almost everywhere for its actual periodic extension. -/
theorem ae_l2WholeLinePotential_property (u : IntervalPairL2) (P : ℂ × ℂ → Prop)
    (hP : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1), P (intervalL2Representative u t)) :
    ∀ᵐ t : ℝ, P (l2WholeLinePotential u t) := by
  have hu : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) 1), P (l2WholeLinePotential u t) := by
    filter_upwards [hP,l2WholeLinePotential_ae_unit u] with t ht he
    rwa [he]
  have hn (n : ℤ) : ∀ᵐ t : ℝ, t ∈ Ioc (n : ℝ) ((n : ℝ)+1) → P (l2WholeLinePotential u t) := by
    have h : ∀ᵐ t ∂volume.restrict (Ioc (n : ℝ) ((n : ℝ)+1)),
        P ((l2WholeLinePotential u ∘ (fun s : ℝ => s-(n : ℝ))) t) :=
      (measurePreserving_period_sub_int n).quasiMeasurePreserving.ae hu
    rw [l2WholeLinePotential_comp_sub_int] at h
    exact (ae_restrict_iff' measurableSet_Ioc).mp h
  filter_upwards [ae_all_iff.mpr hn] with t ht
  apply ht (⌈t⌉-1)
  simp only [Int.cast_sub,Int.cast_one,sub_add_cancel,mem_Ioc]
  constructor
  · linarith [Int.ceil_lt_add_one t]
  · exact Int.le_ceil t

/-- An original physical real-type potential remains Hermitian almost
everywhere after periodization on the whole real line. -/
theorem ae_l2WholeLinePotential_real (u : IntervalPairL2)
    (hu : IsClassicalRealType (intervalL2Representative u)) :
    ∀ᵐ t : ℝ, (l2WholeLinePotential u t).2 =
      (starRingEnd ℂ) (l2WholeLinePotential u t).1 :=
  ae_l2WholeLinePotential_property u (fun v => v.2 = (starRingEnd ℂ) v.1) hu

/-- The same Hermitian relation holds for every original real Hilbert source. -/
theorem ae_source_l2WholeLinePotential_real (φ : CoeffPair 2)
    (hφ : IsRealType (CoeffPair.toMax 2 φ)) :
    ∀ᵐ t : ℝ, (l2WholeLinePotential (sourcePhysicalL2 φ) t).2 =
      (starRingEnd ℂ) (l2WholeLinePotential (sourcePhysicalL2 φ) t).1 :=
  ae_l2WholeLinePotential_real _ ((sourcePhysicalL2_realType_iff φ).mpr hφ)

end NLS.ZakharovShabat
