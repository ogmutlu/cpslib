import CPSLib.Examples.ACASX.ExplicitFormulations.Model

open CPSLib

namespace ACASX

/-- STTT17 Lemma 1, also in `acasx.kyx`. -/
theorem immediate_regions_equivalent :
    ∀ rp hp rv alo r h v w vlo,
      Bounds rp hp rv alo → (w = -1 ∨ w = 1) →
        (Lexpl rp hp rv alo r h v w vlo ↔ Limpl rp hp rv alo r h v w vlo) := sorry

/-- STTT17 Lemma 2 -/
theorem delayed_regions_equivalent :
    ∀ rp hp rv alo ad r h v w vlo d,
      Bounds rp hp rv alo → 0 ≤ ad → (w = -1 ∨ w = 1) →
        (Dexpl rp hp rv alo ad r h v w vlo d ↔ Dimpl rp hp rv alo ad r h v w vlo d) :=
  sorry

/-- STTT17 Lemma 3 -/
theorem two_sided_regions_equivalent :
    ∀ rp hp rv alo aup r h v w vlo vup,
      Bounds rp hp rv alo → alo ≤ aup → (w = -1 ∨ w = 1) →
        (Cexpl rp hp rv alo aup r h v w vlo vup ↔
          Cimpl rp hp rv alo aup r h v w vlo vup) := sorry

/-- STTT17 Lemma 4, with the documented corrections. -/
theorem bounded_regions_equivalent :
    ∀ rp hp rv alo aup tl r h v w vlo vup,
      Bounds rp hp rv alo → alo ≤ aup → (w = -1 ∨ w = 1) →
        (CexplBoundedHat rp hp rv alo aup tl r h v w vlo vup ↔
          CimplBounded rp hp rv alo aup tl 0 r h v w vlo vup) := sorry

/-- STTT17 Lemma 5, both endpoint cases, with the paper's common assumptions. -/
theorem endpoint_cases_redundant :
    ∀ rp hp rv alo aup tl r h v w vlo vloEx vup vupEx,
      Bounds rp hp rv alo → alo ≤ aup → 0 ≤ tl → (w = -1 ∨ w = 1) →
        (let ex := lowerExit alo tl v w vlo
         Lexpl rp hp rv alo (r - rv * tl) (h - ex.1) ex.2 w vloEx →
           horizonCase rp rv tl r → bound15 hp alo tl h v w vlo) ∧
        (let ex := upperExit aup tl v w vup
         Lexpl rp hp rv alo (r - rv * tl) (h - ex.1) ex.2 (-w) vupEx →
           horizonCase rp rv tl r → bound16 hp aup tl h v w vup) := sorry

/-- STTT17 Lemma 6, with corrected endpoints. -/
theorem safeable_regions_equivalent :
    ∀ rp hp rv alo aup tl r h v w vlo vloEx vup vupEx,
      Bounds rp hp rv alo → alo ≤ aup → 0 ≤ tl → (w = -1 ∨ w = 1) →
        (CexplSafeable rp hp rv alo aup tl r h v w vlo vloEx vup vupEx ↔
          CimplSafeable rp hp rv alo aup tl 0 r h v w vlo vloEx vup vupEx) := sorry

end ACASX
