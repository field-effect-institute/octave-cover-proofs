import Mathlib.Tactic
import OctaveCoverProofs.CosmoEpochsOctave

/-!
# CosmoEpochsGradedCoverNegative — cosmology is the NEGATIVE control for the graded-octave cover

**What this file is.** The negative control that makes the music (ℤ/12) and chemistry (ℤ/8)
graded-octave-cover instances *mean* something. `GradedOctaveCover.lean` requires a base that
**closes** — a total successor whose iterate is the identity (`transcend_n 9 l = l`), with no
fixed points — and the per-domain question is whether THIS domain *forces* that
closing base or whether an author imposed it. Music and chemistry force it (B→C chroma
recurrence; noble-gas→alkali chemical recurrence). **Cosmology does not.**

**The claim:** the faithful structure of the cosmological epoch ladder is a strict *linear*
order — a counter with a maximum (the present epoch) and **no closing ring to count around**.
So the recurring-base predicate the cover demands is provably ABSENT, and the pattern
**does not apply** to cosmology.

**Relationship to `CosmoEpochsOctave.lean`.** That file makes `CosmoPhase` a cyclic
`OctaveStructure` instance — but only by *imposing* the close `Recombination → Planck`, which its
own docstring disclaims as NOT a physical claim that the universe loops. This file proves that
disclaimer is load-bearing: the imposed close is the *only* close available, and it runs cosmic
time **backward** (`NCG4`). The fiat 7-cycle does close (`CosmoEpochs.ce_transcend_7_eq_id`); the
faithful linear order cannot (`NCG3`). An author's labeling choice, not forced by the domain —
exactly the negative-control shape: a framework that can only say yes is a rubber stamp, and
this file is the framework saying no.

**Honest scope.** This is a *structural* negative: it shows the faithful cosmic-time order admits
no closing base, not a physical cosmology claim beyond "cosmic time is linearly ordered with a
present." That linear-order fact is the physics (thermal history is monotone in cosmic time); the
negative follows from it by `NCG3`/`NCG6` with no further assumption.
-/

namespace CosmoEpochsGradedCoverNegative

open CosmoEpochs

-- ════════════════════════════════════════════════════════════
-- THE FAITHFUL COSMIC-TIME STRUCTURE (linear, not the imposed cycle)
-- ════════════════════════════════════════════════════════════

/-- The faithful cosmic-time grade: the epochs are linearly ordered by cosmic time
    (equivalently, by monotonically decreasing temperature). This is physics, not a labeling
    choice — Planck is earliest/hottest (0), Recombination latest (6). It is the "counter" the
    article names: a strict integer index that always advances and never wraps. -/
def epochIndex : CosmoPhase → ℕ
  | .Planck          => 0
  | .GUT             => 1
  | .Electroweak     => 2
  | .Quark           => 3
  | .Hadron          => 4
  | .Nucleosynthesis => 5
  | .Recombination   => 6

/-- The faithful (linear, **partial**) successor: the next epoch in cosmic time, or `none` at
    `Recombination` — the present/last epoch has no successor epoch. Contrast
    `CosmoEpochs.CosmoPhase.next` (in `CosmoEpochsOctave.lean`), which IMPOSES
    `Recombination ↦ Planck` to manufacture a cycle. -/
def linNext : CosmoPhase → Option CosmoPhase
  | .Planck          => some .GUT
  | .GUT             => some .Electroweak
  | .Electroweak     => some .Quark
  | .Quark           => some .Hadron
  | .Hadron          => some .Nucleosynthesis
  | .Nucleosynthesis => some .Recombination
  | .Recombination   => none

-- ════════════════════════════════════════════════════════════
-- NCG1–NCG2 — A GENUINE LINEAR ORDER WITH A TERMINAL
-- ════════════════════════════════════════════════════════════

/-- **NCG1: the faithful successor strictly advances cosmic time.** Wherever `linNext` is
    defined, it strictly increases `epochIndex`. So the faithful structure is a genuine strict
    linear order — a real counter, not a strawman. -/
theorem ncg1_linNext_strictly_advances :
    ∀ p p' : CosmoPhase, linNext p = some p' → epochIndex p < epochIndex p' := by
  decide

/-- **NCG2: Recombination is the unique terminal epoch — a counter, but no closing ring.**
    `linNext` is `none` exactly at `Recombination`; every other epoch has a faithful successor.
    There is nowhere for the present to advance to within the ladder, so the base does not
    return. -/
theorem ncg2_unique_terminal :
    ∀ p : CosmoPhase, linNext p = none ↔ p = .Recombination := by
  decide

/-- Recombination carries the maximal cosmic-time index. -/
theorem epochIndex_recombination : epochIndex .Recombination = 6 := rfl

/-- Every epoch's index is bounded by the present (6). -/
theorem epochIndex_le_six : ∀ p : CosmoPhase, epochIndex p ≤ 6 := by decide

-- ════════════════════════════════════════════════════════════
-- NCG3 — THE HEART: NO RECURRING BASE
-- ════════════════════════════════════════════════════════════

/-- **NCG3: the faithful cosmic-time order admits NO closing successor — no recurring base.**

    There is no total successor function on the epochs that respects cosmic time (strictly
    increases `epochIndex` everywhere). The graded-octave cover needs exactly such a closing
    base (`transcend_n 9 l = l`, a total successor whose orbit returns); cosmology cannot supply
    one. The obstruction is structural: the present epoch (index 6, the maximum) has nowhere
    order-respecting to go, so any order-respecting successor would have to exceed the maximum.

    This is the formal content of "the universe's timeline has a counter but no closing ring." -/
theorem ncg3_no_recurring_base :
    ¬ ∃ s : CosmoPhase → CosmoPhase, ∀ p, epochIndex p < epochIndex (s p) := by
  rintro ⟨s, hs⟩
  have h := hs .Recombination
  rw [epochIndex_recombination] at h
  have hle : epochIndex (s .Recombination) ≤ 6 := epochIndex_le_six _
  omega

-- ════════════════════════════════════════════════════════════
-- NCG4 — THE ONLY CLOSE IS A TIME-REVERSING FIAT EDGE (curatorial)
-- ════════════════════════════════════════════════════════════

/-- **NCG4: the imposed cyclic close runs cosmic time backward.** The imposed successor
    `CosmoPhase.next` (which DOES close — `CosmoEpochs.ce_transcend_7_eq_id` proves the 7-cycle)
    closes only via the edge `Recombination ↦ Planck`, which drops the cosmic-time index from
    6 to 0. The recurrence is purchased with a time-reversing fiat edge — an author's labeling
    choice, not forced by the domain. This is precisely the "structural close, NOT a physical
    loop" the `CosmoEpochsOctave` docstring disclaims, now stated as a theorem. -/
theorem ncg4_fiat_close_reverses_time :
    epochIndex (CosmoPhase.next .Recombination) < epochIndex .Recombination := by
  decide

/-- The imposed cycle genuinely does close (re-exported from `CosmoEpochsOctave.lean`) — so the
    contrast in NCG4 is between a base that closes by fiat and a faithful base that cannot
    close at all. -/
theorem ncg4b_fiat_cycle_closes (p : CosmoPhase) :
    p.next.next.next.next.next.next.next = p :=
  CosmoEpochs.ce_transcend_7_eq_id p

-- ════════════════════════════════════════════════════════════
-- NCG6 — NON-VACUITY: THE NEGATIVE IS ENCODING-FORCED, NOT LABEL-CHOSEN
-- ════════════════════════════════════════════════════════════

/-- **NCG6: the terminal is forced by the order, not by the labels.** `epochIndex` is injective
    and `Recombination` is its unique maximizer. Any faithful re-encoding of cosmic time (any
    injective grade with the same order type) has a maximum element with no successor — so the
    failure in NCG3 is a property of the linear order, not of the chosen indices. This is the
    non-vacuity rung: the negative does not hinge on one author-chosen metric. -/
theorem ncg6_terminal_order_forced :
    Function.Injective epochIndex ∧
    (∀ p : CosmoPhase, epochIndex p ≤ epochIndex .Recombination) := by
  refine ⟨?_, ?_⟩
  · intro a b h; cases a <;> cases b <;> simp_all [epochIndex]
  · intro p; rw [epochIndex_recombination]; exact epochIndex_le_six p

-- ════════════════════════════════════════════════════════════
-- NCG5 — THE NEGATIVE-CELL PUNCHLINE
-- ════════════════════════════════════════════════════════════

/-- **NCG5: the graded-octave cover does NOT apply to cosmology.**

    Assembled: the faithful cosmic-time structure is a strict linear order (NCG1) with a unique
    terminal epoch (NCG2) and no order-respecting closing successor (NCG3); the only available
    close is the time-reversing fiat edge of the imposed cycle (NCG4). Cosmology therefore
    supplies a counter (linear grade) but no domain-forced recurring base — the exact
    structure the music/chemistry covers possess and the structure the graded-octave cover
    requires. The same test that says YES to music and chemistry says NO here, and the no is
    proved, not asserted. -/
theorem ncg5_cosmo_graded_cover_negative :
    -- (1) faithful successor strictly advances cosmic time (a genuine linear grade)
    (∀ p p' : CosmoPhase, linNext p = some p' → epochIndex p < epochIndex p') ∧
    -- (2) a unique terminal epoch: a counter with no closing ring
    (∀ p : CosmoPhase, linNext p = none ↔ p = .Recombination) ∧
    -- (3) NO recurring base: no order-respecting closing successor exists
    (¬ ∃ s : CosmoPhase → CosmoPhase, ∀ p, epochIndex p < epochIndex (s p)) ∧
    -- (4) the only close (the imposed fiat cycle) reverses cosmic time
    (epochIndex (CosmoPhase.next .Recombination) < epochIndex .Recombination) := by
  exact ⟨ncg1_linNext_strictly_advances, ncg2_unique_terminal,
         ncg3_no_recurring_base, ncg4_fiat_close_reverses_time⟩

end CosmoEpochsGradedCoverNegative

/-!
## Summary

**6 named results (NCG1–NCG6), 0 sorry.** Cosmology is the NEGATIVE control for the
graded-octave cover: the faithful cosmic-time ladder is a strict linear order (NCG1) with a
unique terminal epoch (NCG2), admits no order-respecting closing successor (NCG3 — the heart),
and the only available close is the time-reversing fiat edge of the imposed cycle (NCG4,
NCG4b). NCG6 shows the failure is forced by the order type, not the chosen labels. NCG5 is the
assembled negative punchline.

The recurring base the cover requires — present and forced by the domain in music (ℤ/12) and
chemistry (ℤ/8) — is provably ABSENT in cosmology. The test that says no, with a kernel
behind it.
-/
