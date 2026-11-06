import NLS.KdV.MiuraHillPsiNumerators
import NLS.KdV.HillHminusOneMiuraContour
import NLS.ComplexAnalysis.QuadraticEnergySheet

/-! Jointly analytic actual Hill energy sheets on the full moving cut
complement of a verified Miura numerator family. These use the already
normalized physical sheet, not an even descent of the odd Dirac root. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV
namespace MiuraHillPsiFamily

/-- The affine energy lies in the principal slit and the selected frequency avoids ALL actual cuts. -/
def energyRootDomain (A : MiuraHillPsiFamily) (c : ℂ) : Set (ℂ × Coeff 2) :=
  {t | t.2 ∈ A.source ∧ t.1+c ∈ slitPlane ∧
    Complex.sqrt (t.1+c) ∈ sourceCanonicalRootDomain (by norm_num) (by norm_num) (hillMiuraDiagonal t.2)}

/-- Joint square-root frequency and actual diagonal Miura source. -/
def energyRootCoordinates (c : ℂ) (t : ℂ × Coeff 2) : ℂ × CoeffPair 2 :=
  (Complex.sqrt (t.1+c),hillMiuraDiagonal t.2)

theorem analytic_energyRootCoordinates (c : ℂ) :
    AnalyticOnNhd ℂ (energyRootCoordinates c) {t : ℂ × Coeff 2 | t.1+c ∈ slitPlane} := by
  intro t ht
  have hs : AnalyticAt ℂ Complex.sqrt (t.1+c) :=
    Complex.differentiableOn_sqrt.analyticAt (isOpen_slitPlane.mem_nhds ht)
  have hz := hs.comp (f := fun x : ℂ × Coeff 2 => x.1+c) (analyticAt_fst.add analyticAt_const)
  have hu := (hillMiuraDiagonal.analyticAt t.2).comp (f := Prod.snd) analyticAt_snd
  exact hz.prod hu

theorem energyRootDomain_open (A : MiuraHillPsiFamily) (c : ℂ) : IsOpen (A.energyRootDomain c) := by
  let S : Set (ℂ × Coeff 2) := {t | t.2 ∈ A.source ∧ t.1+c ∈ slitPlane}
  have hS : IsOpen S :=
    (A.source_open.preimage continuous_snd).inter
      (isOpen_slitPlane.preimage (continuous_fst.add continuous_const))
  have hc : ContinuousOn (energyRootCoordinates c) S :=
    (analytic_energyRootCoordinates c).continuousOn.mono inter_subset_right
  have hroot := A.verified.previous.previous.previous.criticalOffsets.previous.previous.joint
  have he : A.energyRootDomain c =
      S ∩ energyRootCoordinates c ⁻¹' sourceCanonicalRootJointDomain (by norm_num) (by norm_num) A.originalDomain := by
    ext t
    constructor
    · rintro ⟨hu,hs,hz⟩
      exact ⟨⟨hu,hs⟩,A.verified.subset hu,hz⟩
    · rintro ⟨⟨hu,hs⟩,_,hz⟩
      exact ⟨hu,hs,hz⟩
  rw [he]
  exact hc.isOpen_inter_preimage hS hroot.1

/-- The transferred energy root is jointly analytic in energy and the original L2 lift. -/
theorem analytic_energyRoot (A : MiuraHillPsiFamily) (c : ℂ) :
    AnalyticOnNhd ℂ (fun t : ℂ × Coeff 2 => hillHminusMiuraRoot t.2 c t.1) (A.energyRootDomain c) := by
  intro t ht
  have hroot := A.verified.previous.previous.previous.criticalOffsets.previous.previous.joint
  have hp : energyRootCoordinates c t ∈
      sourceCanonicalRootJointDomain (by norm_num) (by norm_num) A.originalDomain :=
    ⟨A.verified.subset ht.1,ht.2.2⟩
  exact (hroot.2 _ hp).comp (f := energyRootCoordinates c)
    (analytic_energyRootCoordinates c t ht.2.1)

theorem energyRoot_ne_zero (A : MiuraHillPsiFamily) (c : ℂ) (t : ℂ × Coeff 2)
    (ht : t ∈ A.energyRootDomain c) : hillHminusMiuraRoot t.2 c t.1 ≠ 0 :=
  sourceCanonicalRoot_ne_zero_off_gaps (by norm_num) (by norm_num) _ _ ht.2.2

/-- The actual energy differential coefficient on the verified moving root domain. -/
def differential (A : MiuraHillPsiFamily) (n : ℕ+) (c : ℂ) (t : ℂ × Coeff 2) : ℂ :=
  A.numerator n (t.1+c,t.2)/hillHminusMiuraRoot t.2 c t.1

theorem analytic_differential (A : MiuraHillPsiFamily) (n : ℕ+) (c : ℂ) :
    AnalyticOnNhd ℂ (A.differential n c) (A.energyRootDomain c) := by
  intro t ht
  exact (A.analytic_shifted_numerator n c t ⟨mem_univ _,ht.1⟩).div
    (A.analytic_energyRoot c t ht) (A.energyRoot_ne_zero c t ht)

/-- Its squared denominator is the ACTUAL native Hill radicand for every valid shifted image. -/
theorem energyRoot_sq (A : MiuraHillPsiFamily) (q : PeriodOneHminusOne) (c : ℂ) (t : ℂ × Coeff 2)
    (ht : t ∈ A.energyRootDomain c)
    (hi : periodOneMiura t.2 = q+periodOneL2Inclusion (lp.single 2 0 c)) :
    hillHminusMiuraRoot t.2 c t.1^2 = hillHminusRadicand q t.1 :=
  hillHminusMiuraRoot_sq q t.2 c t.1 hi ht.2.2

/-- Positive frequency points give exactly the same selected energy sheet. -/
theorem squared_energy_mem_rootDomain (A : MiuraHillPsiFamily) (u : Coeff 2) (hu : u ∈ A.source)
    (c z : ℂ) (hz : 0 < z.re)
    (hr : z ∈ sourceCanonicalRootDomain (by norm_num) (by norm_num) (hillMiuraDiagonal u)) :
    (z^2-c,u) ∈ A.energyRootDomain c := by
  refine ⟨hu,?_,?_⟩
  · simpa only [sub_add_cancel] using sq_mem_slitPlane_of_re_pos z hz
  · simpa only [sub_add_cancel,sqrt_sq_of_re_pos z hz] using hr

end MiuraHillPsiFamily
end NLS.KdV
