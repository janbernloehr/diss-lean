import NLS.Articles.KdVKdV2Frequencies.PhysicallyOrientedRoughPackets
import NLS.KdV.HillHminusEtaGapRegularity
import NLS.SequenceSpaces.PositiveReciprocalMembership

/-! # Actual packet membership detects arbitrary rough source regularity -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies
open NLS.KdV
variable {q0 : PeriodOneHminusOne}

/-- The SAME actual full packet detects every Sobolev order at EVERY
real rough source in its original ball. Initial L2 membership is not assumed. -/
theorem RoughAbelianFourierDataAt.sobolev_iff_weighted_packet_mem
    (D : RoughAbelianFourierDataAt q0) (q : PeriodOneHminusOne)
    (hq : q ∈ ball q0 D.radius) (hr : IsRealPeriodOneHminusOne q)
    (s : ℝ) (hs : -1 ≤ s) :
    Memℓp (fun j => (Weight.sobolev s j : ℂ)*q.val j) 2 ↔
      Memℓp (fun j => (Weight.sobolev (s+1) j : ℂ)*D.packet q j) 2 := by
  have hreal := D.real_lift q (D.source_domain hq).1.1 hr
  have hEta := D.chart.sobolev_iff_positive_eta_mem D.roots q (D.source_domain hq) hreal s hs
  have hrec (j : ℤ) (hj : 0 < j) : D.symbol q j*D.reciprocal q j = 1 := by
    let n : ℕ+ := ⟨j.toNat,by omega⟩
    have hn : (n : ℤ) = j := by change (j.toNat : ℤ) = j; omega
    simpa only [hn] using ((D.symbol_data q hq).2.2.2 n).2.2.2
  have hprod := Coeff.memlp_positive_product_iff (D.symbol q) (D.reciprocal q) hrec
    (fun j => (Weight.sobolev (s+1) j : ℂ)*D.chart.sourceEtaSequence q j)
  have hp (j : ℤ) : D.packet q j = D.symbol q j*D.chart.sourceEtaSequence q j := by
    rw [(D.packet_data q hq).1]
    rfl
  have he : (fun j : ℤ => if 0 < j then D.symbol q j*
      ((Weight.sobolev (s+1) j : ℂ)*D.chart.sourceEtaSequence q j) else 0) =
      (fun j => (Weight.sobolev (s+1) j : ℂ)*D.packet q j) := by
    funext j
    by_cases hj : 0 < j
    · rw [if_pos hj,hp]
      ring
    · rw [if_neg hj,(D.packet_data q hq).2.2 j (by omega),mul_zero]
  rw [he] at hprod
  exact hEta.trans hprod.symm

/-- The ONE fixed physical sign selection retains this exact criterion. -/
theorem PhysicallyOrientedRoughPacketAt.sobolev_iff_weighted_positive_mem
    (D : PhysicallyOrientedRoughPacketAt q0) (q : PeriodOneHminusOne)
    (hq : q ∈ ball q0 D.data.radius) (hr : IsRealPeriodOneHminusOne q)
    (s : ℝ) (hs : -1 ≤ s) :
    Memℓp (fun j => (Weight.sobolev s j : ℂ)*q.val j) 2 ↔
      Memℓp (fun j => (Weight.sobolev (s+1) j : ℂ)*D.positive q j) 2 := by
  apply (D.data.sobolev_iff_weighted_packet_mem q hq hr s hs).trans
  have he (j : ℤ) : ‖(Weight.sobolev (s+1) j : ℂ)*D.positive q j‖ =
      ‖(Weight.sobolev (s+1) j : ℂ)*D.data.packet q j‖ := by
    change ‖(Weight.sobolev (s+1) j : ℂ)*Coeff.signChange D.signs (D.data.packet q) j‖ = _
    rw [Coeff.signChange_apply]
    cases D.signs j <;> simp only [Bool.false_eq_true,↓reduceIte,norm_mul,norm_neg]
  exact ⟨fun h => h.mono' (fun j => (he j).le),fun h => h.mono' (fun j => (he j).symm.le)⟩

end NLS.Articles.KdVKdV2Frequencies
