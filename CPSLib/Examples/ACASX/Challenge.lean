import CPSLib.Examples.ACASX.Model

open CPSLib

namespace ACASX

/-- STTT17 Theorem 1, with the stronger postcondition (+ Limpl) from `acasx.kyx`. -/
theorem immediate_safe :
    ∀ rp hp rv alo r h v w vlo,
      Bounds rp hp rv alo → Sense w → Limpl rp hp rv alo r h v w vlo →
        ∀ res ∈ SetM.run (immediate rp hp rv alo r h v w vlo),
          NoNMAC rp hp res.r res.h ∧
            Limpl rp hp rv alo res.r res.h res.v res.w res.vlo := sorry

/-- STTT17 Theorem 2, with the stronger postcondition (+ Dimpl) from
`safe_delay_implicit.kyx` -/
theorem delayed_safe :
    ∀ rp hp rv alo ad δ ε r h v w vlo d,
      Bounds rp hp rv alo → (0 ≤ ad ∧ 0 ≤ δ ∧ 0 ≤ ε) → Sense w →
      Dimpl rp hp rv alo ad r h v w vlo d →
        ∀ res ∈ SetM.run (delayed rp hp rv alo ad δ ε r h v w vlo d),
          NoNMAC rp hp res.r res.h ∧
            Dimpl rp hp rv alo ad res.r res.h res.v res.w res.vlo res.d := sorry

/-- STTT17 Theorem 3, also in `acasxtwosided.kyx`. -/
theorem two_sided_safe :
    ∀ rp hp rv alo aup r h v w vlo vup,
      Bounds rp hp rv alo → alo ≤ aup → Sense w →
      Cimpl rp hp rv alo aup r h v w vlo vup →
        ∀ res ∈ SetM.run (twoSided rp hp rv alo aup r h v w vlo vup),
          NoNMAC rp hp res.r res.h := sorry

/-- STTT17 Theorem 4, with weaker precondition (`0 < aup` instead of `alo ≤ aup`) and
stronger postcondition (+ Sense, + CimplBounded), following `bounded_implicit.kyx`.
The paper version is equivalent to the case `t=0`. -/
theorem bounded_safe :
    ∀ rp hp rv alo aup tl r h v w vlo vup t,
      Bounds rp hp rv alo ∧ 0 < aup → Sense w → (t ≤ tl ∨ tl < 0) →
      CimplBounded rp hp rv alo aup tl t r h v w vlo vup →
        ∀ res ∈ SetM.run (bounded rp hp rv alo aup tl r h v w vlo vup t),
          NoNMAC rp hp res.r res.h ∧ Sense res.w ∧ (res.t ≤ tl ∨ tl < 0) ∧
          CimplBounded rp hp rv alo aup tl res.t res.r res.h res.v res.w res.vlo res.vup
            := sorry

/-- STTT17 Theorem 5, with stronger postcondition (+ Sense, + CimplSafeable), following
`AcasXSafeable.scala`. The paper version is equivalent to the case `t=0`. -/
theorem safeable_safe :
    ∀ rp hp rv alo aup tl vloEx vupEx r h v w vlo vup t,
      Bounds rp hp rv alo → alo ≤ aup → 0 ≤ tl → Sense w → (t ≤ tl ∨ tl < 0) →
      CimplSafeable rp hp rv alo aup tl t r h v w vlo vloEx vup vupEx →
        ∀ res ∈ SetM.run (safeable rp hp rv alo aup tl vloEx vupEx r h v w vlo vup t),
          NoNMAC rp hp res.r res.h ∧ Sense res.w ∧ (res.t ≤ tl ∨ tl < 0) ∧
            CimplSafeable rp hp rv alo aup tl res.t res.r res.h res.v
              res.w res.vlo vloEx res.vup vupEx := sorry

/-- STTT17 Proposition 1 -/
theorem horizontal_reduction :
    ∀ rp rx ry rv x y s n,
      HorizontalCoordinates rx ry rv x y s n →
        ∀ x_res y_res s_res n_res,
          (x_res, y_res, s_res, n_res) ∈
            SetM.run (evolve (horizontalMotion rx ry rv) (fun _ => True) (x, y, s, n)) →
            (rp ^ 2 < x_res ^ 2 + y_res ^ 2 ↔ rp ^ 2 - n_res ^ 2 < s_res ^ 2) := sorry

end ACASX
