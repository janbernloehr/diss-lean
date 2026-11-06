import NLS.KdV.HillOriginalOffIndexSourceSeries
import NLS.KdV.HillSummedRegularCorrection

noncomputable section
set_option autoImplicit false
open Set Complex NLS.ZakharovShabat
open scoped ComplexConjugate
namespace NLS.KdV.HillHminusPsiChart
variable (P : HillHminusPsiChart) (q : RealPeriodOneHillPotential)
  (hq : hillOriginalHminusSource q.val∈P.source)
  (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
    P.miura.lift a (-k)=conj (P.miura.lift a k))
  (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
  (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2)
  (H : SourceLemma12_12Data (by norm_num) (by norm_num)
    P.family.originalDomain P.family.domain P.family.roots)
include hq hreal houtside hshift H

/-- Exact separation of the own-index term in the ORIGINAL full scalar
series. Summability is derived from the checked off-index comparison. -/
theorem originalFullCorrection_eq_own_add_offIndex (n : ℕ+) :
    hillSummedRegularAbelianCorrection q.val q.property.1 q.property.2 n n.pos=
      hillRegularAbelianCorrection q.val q.property.1 q.property.2 n n.pos n n.pos+
        hillOriginalOffIndexCorrection n q := by
  let f : ℕ → ℂ := fun j => hillRegularAbelianCorrection q.val q.property.1 q.property.2 n n.pos (j+1) (by omega)
  let k : ℕ := (n:ℕ)-1
  have hn := n.pos
  have hk : k+1=(n:ℕ) := by dsimp only [k];omega
  have hs : Summable (fun j => hillOriginalOffIndexCorrectionTerm n q j) :=
    (P.originalOffIndexCorrection_summable_norm q hq hreal houtside c hshift H n).of_norm
  have he : f=fun j => hillOriginalOffIndexCorrectionTerm n q j+(if j=k then f k else 0) := by
    funext j
    by_cases hj : j+1=(n:ℕ)
    · have hjk : j=k := by dsimp only [k];omega
      subst j
      simp only [hillOriginalOffIndexCorrectionTerm,if_pos hj,ite_true,zero_add]
    · have hjk : j≠k := by intro h;apply hj;rw [h,hk]
      simp only [hillOriginalOffIndexCorrectionTerm,if_neg hj,if_neg hjk,add_zero,f]
  change (∑' j : ℕ, f j)=_+_
  rw [he,hs.tsum_add (hasSum_ite_eq k (f k)).summable,tsum_ite_eq,add_comm]
  change f k+hillOriginalOffIndexCorrection n q=_+_
  dsimp only [f]
  simp only [hk]

/-- The ORIGINAL full correction has exactly these finite own-index,
central and negative-selected contributions to the signed source sum.
No endpoint or collapsed-gap restriction is imposed. -/
theorem originalFullCorrection_eq_signed_source_finite_terms (n : ℕ+) :
    hillSummedRegularAbelianCorrection q.val q.property.1 q.property.2 n n.pos=
      hillRegularAbelianCorrection q.val q.property.1 q.property.2 n n.pos n n.pos+
        P.sourceBetaCorrection (n:ℕ) (hillOriginalHminusSource q.val)-
        sourceAngularBeta (by norm_num) (by norm_num) ((n:ℕ):ℤ) 0 P.family.roots
          (P.dirichletSource (hillOriginalHminusSource q.val))-
        sourceAngularBeta (by norm_num) (by norm_num) ((n:ℕ):ℤ) (-((n:ℕ):ℤ)) P.family.roots
          (P.dirichletSource (hillOriginalHminusSource q.val)) := by
  have ha := P.mem_sourceBetaDomain_of_real (hillOriginalHminusSource q.val) hq
    (hreal _ hq.1 (hillOriginalHminusSource_real q.val q.property.2))
  rw [P.originalFullCorrection_eq_own_add_offIndex q hq hreal houtside c hshift H n,
    P.originalOffIndexCorrection_eq_sourcePaired q hq hreal houtside c hshift H n,
    P.sourcePairedBetaCorrection_eq H n _ ha]
  ring

end NLS.KdV.HillHminusPsiChart
