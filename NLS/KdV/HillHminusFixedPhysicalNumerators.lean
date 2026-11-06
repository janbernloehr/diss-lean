import NLS.KdV.HillHminusNumeratorDecay

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.KdV

/-- The actual all-index analytic energy numerator is literally the
FIXED original physical normalized Hill numerator. All decay and
normalization obligations are proved, including at collapsed gaps. -/
theorem HillHminusPsiChart.numerator_eq_original (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val∈P.source)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k)=conj (P.miura.lift a k))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
    (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2) (n : ℕ+) :
    (fun E => P.numerator n (E,hillOriginalHminusSource q.val))=
      hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n n.pos := by
  exact P.numerator_eq_original_of_product_decay q hq hreal houtside c hshift n
    (fun roots hroots ε hε => P.numerator_full_product_decay q n roots hroots ε hε)

/-- The actual common analytic differential is exactly the ORIGINAL
physical normalized Abelian differential on its valid physical cut. -/
theorem HillHminusPsiChart.differential_eq_original_normalized (P : HillHminusPsiChart)
    (q : RealPeriodOneHillPotential) (hq : hillOriginalHminusSource q.val∈P.source)
    (hreal : ∀ a∈P.miura.domain, IsRealPeriodOneHminusOne a → ∀ k : ℤ,
      P.miura.lift a (-k)=conj (P.miura.lift a k))
    (houtside : hillHminusRadicand (hillOriginalHminusSource q.val) (-P.miura.energyShift)≠0)
    (c : ℝ) (hshift : P.miura.energyShift=(c:ℂ)^2) (n : ℕ+) (E : ℂ)
    (hE : (E,hillOriginalHminusSource q.val)∈P.rootDomain)
    (hcut : E∈hillL2RealCutDomain q.val q.property.1 q.property.2) :
    P.differential n (E,hillOriginalHminusSource q.val)=
      hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n n.pos E/
        hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E := by
  rw [P.differential_eq_original_root q
    (hreal _ hq.1 (hillOriginalHminusSource_real q.val q.property.2))
    (c^2) (by simpa only [ofReal_pow] using hshift) n E hE hcut,
    congrFun (P.numerator_eq_original q hq hreal houtside c hshift n) E]

/-- One common complex H-minus-one neighborhood and one common original
real neighborhood support analytic extensions of EVERY fixed original
normalized numerator, with the checked common all-index estimates. -/
theorem exists_hillOriginal_all_numerators_common_hminus_extension
    (q : RealPeriodOneHillPotential) (M : ℝ) :
    ∃ P : HillHminusPsiChart, ∃ c : ℝ, ∃ W : Set RealPeriodOneHillPotential,
      0<c ∧ M<c ∧ P.miura.energyShift=(c:ℂ)^2 ∧
      IsOpen P.source ∧ hillOriginalHminusSource q.val∈P.source ∧
      IsOpen W ∧ q∈W ∧
      SourceLemma12_12Data (by norm_num) (by norm_num)
        P.family.originalDomain P.family.domain P.family.roots ∧
      (∀ n : ℕ+, AnalyticOnNhd ℂ (P.numerator n) (univ ×ˢ P.source)) ∧
      ∀ p∈W, ∀ n : ℕ+, ∀ E : ℂ,
        P.numerator n (E,hillOriginalHminusSource p.val)=
          hillAbelianSelectedGlobalPsi p.val p.property.1 p.property.2 n n.pos E := by
  obtain ⟨P,c,hc,hMc,hshift,hqP,hreal,houtside,hest⟩ :=
    exists_hillHminusPsiChart_real_form_outside_shift (hillOriginalHminusSource q.val)
      (hillOriginalHminusSource_real q.val q.property.2) M
  let W : Set RealPeriodOneHillPotential := {p | hillOriginalHminusSource p.val∈P.source}
  have hW : IsOpen W := P.source_open.preimage
    (hillOriginalHminusSource.continuous.comp continuous_subtype_val)
  refine ⟨P,c,W,hc,hMc,hshift,P.source_open,hqP,hW,hqP,hest,P.analytic_numerator,?_⟩
  intro p hp n E
  exact congrFun (P.numerator_eq_original p hp hreal (houtside _ hp.1) c hshift n) E

end NLS.KdV
