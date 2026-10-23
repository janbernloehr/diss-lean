import NLS.FunctionalAnalysis.RealSignedSheet
import NLS.ZakharovShabat.SourceDirichletRealSpectralSheet

/-! # Real and literal signed coordinates for the actual Dirichlet sheet

The actual complex algebraic sheet over a real source is homeomorphic to
the corresponding real sheet. Its height is the original discriminant
squared minus four. Literal signs with the branch-quotient topology give
the same sheet, including collapsed gaps.
-/
noncomputable section
open Set Complex NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual nonnegative sheet height over a real periodic gap. -/
def sourceDirichletSheetHeight (hp : p ≠ ⊤) (φ : realTypeSourceSubmodule p) (x : ℝ) : ℝ :=
  (canonicalDiscriminant hp (periodOnePotential φ.val) (x : ℂ)).re^2-4

/-- The full real sheet in base/terminal coordinates. -/
def sourceDirichletRealSheet (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Icc
    (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
    (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re ∧
    z.2^2 = sourceDirichletSheetHeight hp φ z.1}

/-- Literal eigenvalue/sign data, carrying the topology of two branches joined at zero height. -/
abbrev SourceSignedDirichletSheet (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :=
  RealSignedSheet (sourceDirichletSheetHeight hp φ)
    (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
    (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re

/-- The actual sheet height is continuous on the real axis. -/
theorem continuous_sourceDirichletSheetHeight (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) : Continuous (sourceDirichletSheetHeight hp φ) :=
  ((continuous_re.comp ((analyticOnNhd_canonicalDiscriminant hp hp1 _
    (periodOnePotential_mem φ.val)).continuous.comp continuous_ofReal)).pow 2).sub continuous_const

/-- The actual height is nonnegative throughout every closed real periodic gap. -/
theorem sourceDirichletSheetHeight_nonneg (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    ∀ x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re,
      0 ≤ sourceDirichletSheetHeight hp φ x := by
  intro x hx
  exact sub_nonneg.mpr (discriminant_re_sq_ge_four_of_mem_canonicalGap hp hp1 _
    (periodOnePotential_mem φ.val) (isRealType_periodOnePotential φ.val φ.property) n x hx)

/-- Zero height occurs exactly at the actual periodic endpoints, also when they coincide. -/
theorem sourceDirichletSheetHeight_zero_iff (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) (x : ℝ)
    (hx : x ∈ Icc
      (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re
      (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re) :
    sourceDirichletSheetHeight hp φ x = 0 ↔
      x = (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re ∨
      x = (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re := by
  let L := canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n
  let R := canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n
  let Δ := canonicalDiscriminant hp (periodOnePotential φ.val)
  have hreal := isRealType_periodOnePotential φ.val φ.property
  change x ∈ Icc L.re R.re at hx
  change sourceDirichletSheetHeight hp φ x = 0 ↔ x = L.re ∨ x = R.re
  constructor
  · intro hz
    by_contra hn
    push Not at hn
    have hi : x ∈ Ioo L.re R.re := ⟨lt_of_le_of_ne hx.1 hn.1.symm,lt_of_le_of_ne hx.2 hn.2⟩
    have ht := two_lt_norm_discriminant_of_mem_canonicalGap_interior hp hp1 _
      (periodOnePotential_mem φ.val) hreal n x hi
    have hs := norm_canonicalDiscriminant_sq_of_realType hp hp1 _
      (periodOnePotential_mem φ.val) hreal x
    change (Δ (x : ℂ)).re^2-4 = 0 at hz
    change 2 < ‖Δ (x : ℂ)‖ at ht
    change ‖Δ (x : ℂ)‖^2 = (Δ (x : ℂ)).re^2 at hs
    nlinarith
  · intro he
    have hLR := canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 _
      (periodOnePotential_mem φ.val) hreal n
    have hl : (L.re : ℂ) = L := Complex.ext rfl (by simpa only [ofReal_im] using hLR.1.symm)
    have hr : (R.re : ℂ) = R := Complex.ext rfl (by simpa only [ofReal_im] using hLR.2.symm)
    have hd := canonicalPeriodicEndpoints_discriminant_of_realType hp hp1 _
      (periodOnePotential_mem φ.val) hreal n
    change Δ L = (if n % 2 = 0 then 2 else -2) ∧ Δ R = (if n % 2 = 0 then 2 else -2) at hd
    change (Δ (x : ℂ)).re^2-4 = 0
    rcases he with rfl | rfl
    · rw [hl,hd.1]
      split_ifs <;> norm_num
    · rw [hr,hd.2]
      split_ifs <;> norm_num

/-- The literal zero sign is exactly the endpoint convention in the source's signed gap. -/
theorem sourceSignedDirichletSheet_sign_zero_iff_endpoint
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ)
    (q : SourceSignedDirichletSheet hp hp1 φ n) :
    q.sign = 0 ↔
      q.base = (canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re ∨
      q.base = (canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n).re :=
  q.sign_zero_iff.trans (sourceDirichletSheetHeight_zero_iff hp hp1 φ n q.base q.base_mem)

/-- The actual signed-gap topology is the quotient of its two compact interval branches. -/
theorem isQuotientMap_sourceSignedDirichletSheet_branches
    (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : realTypeSourceSubmodule p) (n : ℤ) :
    Topology.IsQuotientMap (RealSignedSheet.branchMap (sourceDirichletSheetHeight_nonneg hp hp1 φ n)) :=
  RealSignedSheet.isQuotientMap_branchMap (sourceDirichletSheetHeight_nonneg hp hp1 φ n)
    (continuous_sourceDirichletSheetHeight hp hp1 φ)

/-- Real-coordinate inclusion identifies the original complex algebraic sheet with its full real sheet. -/
def sourceDirichletRealSheetHomeomorph (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    sourceDirichletSpectralSheet hp hp1 n φ.val ≃ₜ sourceDirichletRealSheet hp hp1 φ n := by
  let Δ := canonicalDiscriminant hp (periodOnePotential φ.val)
  let L := canonicalPeriodicLeft hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n
  let R := canonicalPeriodicRight hp hp1 (periodOnePotential φ.val) (periodOnePotential_mem φ.val) n
  have hreal := isRealType_periodOnePotential φ.val φ.property
  have hΔim (x : ℝ) : (Δ (x : ℂ)).im = 0 :=
    canonicalDiscriminant_im_eq_zero_of_realType hp hp1 _ (periodOnePotential_mem φ.val) hreal x
  have hLRim : L.im = 0 ∧ R.im = 0 :=
    canonicalPeriodicEndpoints_im_eq_zero_of_realType hp hp1 _ (periodOnePotential_mem φ.val) hreal n
  let f : sourceDirichletSpectralSheet hp hp1 n φ.val → sourceDirichletRealSheet hp hp1 φ n := fun q =>
    ⟨(q.val.1.re,q.val.2.re),by
      refine ⟨sourcePeriodicSegment_re_mem_Icc hp hp1 φ.val n q.val.1 q.property.1,?_⟩
      have hr := sourceDirichletSpectralSheet_im_eq_zero hp hp1 φ n q.val q.property
      have hc : (q.val.1.re : ℂ) = q.val.1 := Complex.ext rfl (by simpa only [ofReal_im] using hr.1.symm)
      have hD : (Δ q.val.1).im = 0 := by rw [← hc]; exact hΔim _
      have hs := congrArg Complex.re q.property.2
      change (q.val.2^2).re = ((Δ q.val.1)^2-4).re at hs
      simp only [pow_two,mul_re,sub_re,hr.2,hD,mul_zero,sub_zero,
        show (4 : ℂ).re = 4 from rfl] at hs
      change q.val.2.re^2 = (Δ (q.val.1.re : ℂ)).re^2-4
      rw [hc]
      nlinarith⟩
  let g : sourceDirichletRealSheet hp hp1 φ n → sourceDirichletSpectralSheet hp hp1 n φ.val := fun q =>
    ⟨((q.val.1 : ℂ),(q.val.2 : ℂ)),by
      have hq : q.val.1 ∈ Icc L.re R.re := q.property.1
      refine ⟨?_,?_⟩
      · have hseg : q.val.1 ∈ segment ℝ L.re R.re := by
          rw [segment_eq_Icc (hq.1.trans hq.2)]
          exact hq
        have hmem := mem_image_of_mem Complex.ofRealAm.toLinearMap.toAffineMap hseg
        rw [image_segment] at hmem
        change (q.val.1 : ℂ) ∈ segment ℝ (L.re : ℂ) (R.re : ℂ) at hmem
        have hL : (L.re : ℂ) = L := Complex.ext rfl (by simpa only [ofReal_im] using hLRim.1.symm)
        have hR : (R.re : ℂ) = R := Complex.ext rfl (by simpa only [ofReal_im] using hLRim.2.symm)
        change (q.val.1 : ℂ) ∈ segment ℝ L R
        simpa only [hL,hR] using hmem
      · change (q.val.2 : ℂ)^2 = (Δ (q.val.1 : ℂ))^2-4
        apply Complex.ext
        · have hs : q.val.2^2 = (Δ (q.val.1 : ℂ)).re^2-4 := q.property.2
          simpa only [pow_two,mul_re,sub_re,ofReal_re,ofReal_im,hΔim q.val.1,mul_zero,sub_zero,
            show (4 : ℂ).re = 4 from rfl] using hs
        · simp only [pow_two,mul_im,sub_im,ofReal_re,ofReal_im,hΔim q.val.1,mul_zero,zero_mul,zero_add,
            show (4 : ℂ).im = 0 from rfl,sub_zero]⟩
  refine { toFun := f, invFun := g, left_inv := ?_, right_inv := ?_, continuous_toFun := ?_, continuous_invFun := ?_ }
  · intro q
    apply Subtype.ext
    have hr := sourceDirichletSpectralSheet_im_eq_zero hp hp1 φ n q.val q.property
    change ((q.val.1.re : ℂ),(q.val.2.re : ℂ)) = q.val
    apply Prod.ext
    · exact Complex.ext rfl (by simpa only [ofReal_im] using hr.1.symm)
    · exact Complex.ext rfl (by simpa only [ofReal_im] using hr.2.symm)
  · intro q
    apply Subtype.ext
    rfl
  · apply Continuous.subtype_mk
    exact ((continuous_re.comp continuous_fst).comp continuous_subtype_val).prodMk
      ((continuous_re.comp continuous_snd).comp continuous_subtype_val)
  · apply Continuous.subtype_mk
    exact ((continuous_ofReal.comp continuous_fst).comp continuous_subtype_val).prodMk
      ((continuous_ofReal.comp continuous_snd).comp continuous_subtype_val)

/-- The original algebraic sheet has exactly the topology of its literal signed real coordinates. -/
def sourceDirichletSignedSheetHomeomorph (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ) :
    sourceDirichletSpectralSheet hp hp1 n φ.val ≃ₜ SourceSignedDirichletSheet hp hp1 φ n :=
  (sourceDirichletRealSheetHomeomorph hp hp1 φ n).trans RealSignedSheet.homeomorphSheet.symm

@[simp] theorem sourceDirichletSignedSheetHomeomorph_base (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ)
    (q : sourceDirichletSpectralSheet hp hp1 n φ.val) :
    (sourceDirichletSignedSheetHomeomorph hp hp1 φ n q).base = q.val.1.re := rfl

@[simp] theorem sourceDirichletSignedSheetHomeomorph_sign (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceSubmodule p) (n : ℤ)
    (q : sourceDirichletSpectralSheet hp hp1 n φ.val) :
    (sourceDirichletSignedSheetHomeomorph hp hp1 φ n q).sign = SignType.sign q.val.2.re := rfl

end NLS.ZakharovShabat
