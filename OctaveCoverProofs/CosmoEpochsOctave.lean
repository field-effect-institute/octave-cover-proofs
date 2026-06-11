import OctaveCoverProofs.OctaveStructure
import Mathlib.Tactic

/-!
# CosmoEpochsOctave — The Standard Early-Universe Epoch Ladder as a Cyclic 7-Phase Structure

This file encodes the standard early-universe epoch ladder

    Planck → GUT → Electroweak → Quark → Hadron → Nucleosynthesis → Recombination
    ╰──── PRE-BARYON ─────╯   ╰──── BARYON-FORMATION ──────╯   ╰─ STRUCTURE ─╯

as an instance of `OctaveStructure` (a finite cyclic phase structure with
a 3-way segment assignment and an algebra-class labelling) and proves 20
theorems about the encoded order structure.

**Scope.** Everything proved here is about the *encoded* finite structure.
The choice of phases, segments, shock markers, and class labels is a
modeling choice, stated explicitly below; the proofs certify the shape of
the encoding, not the physics. In particular the cyclic close
(`Recombination → Planck`) is a structural device required by the
typeclass (a no-fixed-point successor on a finite type) — it is NOT a
physical claim that the universe loops. The companion file
`CosmoEpochsGradedCoverNegative` makes that point formally: the physical
epoch order admits no time-respecting cyclic close.

## Segment assignment

The 3-3-1 partition groups phases by physical regime:

| Segment | Phases | Physical regime |
|---------|--------|------------------|
| 0 (PRE-BARYON)         | Planck, GUT, Electroweak             | Forces unifying / EW-pre-break |
| 1 (BARYON-FORMATION)   | Quark, Hadron, Nucleosynthesis       | EW broken; matter formation |
| 2 (STRUCTURE)          | Recombination                        | Photon-decoupled; CMB onward |

## Shock encoding

`isShock` marks the three textbook **symmetry-breaking events** —
strong-decoupling at GUT scale, EW symmetry breaking, and the BBN transit
at the radiation/matter boundary. QCD confinement (Quark→Hadron) and n/p
freeze-out (Hadron→Nucleosynthesis) are class-transitions but NOT
symmetry-breaking-grade events (lattice QCD: crossover at physical
light-quark masses; n/p decoupling: freeze-out, not symmetry breaking).
So `isShock = {GUT, Electroweak, Nucleosynthesis}`, with `GUT` the one
shock that fires *inside* a segment rather than at a segment boundary.

Three positions are **segment boundaries** (the segment changes on `next`):

- `Electroweak` (segment 0→1, mi-fa)
- `Nucleosynthesis` (segment 1→2, la-si)
- `Recombination` (segment 2→0, si-do transcend)

Intersection: `{Electroweak, Nucleosynthesis}` — the 2 mi-fa/la-si shocks
that coincide with segment boundaries. Intra-segment shock: `{GUT}` — the
strong-decoupling event that fires *inside* segment 0, not at its
boundary. This 1/3 intra-segment-shock fraction is the structural signal
separating this encoding from instances that model designed processes,
all of which satisfy `isShock ⊆ isBoundary` (see CE10–CE11).

## Algebra-class assignment

Each phase carries an `(id, tag)` label; the tag strings are fixed
descriptive names (another modeling choice):

| Phase | id | tag |
|-------|----|----|
| Planck            | 0 | `StructuredAbsenceInference` |
| GUT               | 1 | `SoftToBindingTransition` |
| Electroweak       | 2 | `BoundaryPredicate` |
| Quark             | 3 | `TransientToDurableTransition` |
| Hadron            | 3 | `TransientToDurableTransition` |
| Nucleosynthesis   | 3 | `TransientToDurableTransition` |
| Recombination     | 4 | `ResultAsRowColumnInput` |

5 distinct `(id, tag)` pairs over 7 positions; the three matter-formation
phases (Quark, Hadron, Nucleosynthesis) share a single class of
cardinality 3.
-/

namespace CosmoEpochs

-- ═══════════════════════════════════════════════════
-- COSMOLOGICAL EPOCHS — 7 PHASES
-- ═══════════════════════════════════════════════════

/-- The seven phases of the standard early-universe ladder.

    PRE-BARYON (Planck, GUT, Electroweak): forces unifying or recently
    decoupled; pre-EW-symmetry-breaking; high-energy regime.
    BARYON-FORMATION (Quark, Hadron, Nucleosynthesis): post-EW matter
    formation; free quarks → confined hadrons → light nuclei.
    STRUCTURE (Recombination): photon-decoupled; CMB → atoms → galaxies. -/
inductive CosmoPhase where
  | Planck
  | GUT
  | Electroweak
  | Quark
  | Hadron
  | Nucleosynthesis
  | Recombination
  deriving DecidableEq, Repr, BEq

instance : Fintype CosmoPhase where
  elems := ⟨[CosmoPhase.Planck, CosmoPhase.GUT, CosmoPhase.Electroweak,
              CosmoPhase.Quark, CosmoPhase.Hadron,
              CosmoPhase.Nucleosynthesis, CosmoPhase.Recombination],
              by decide⟩
  complete p := by cases p <;> decide

namespace CosmoPhase

/-- Cyclic successor: Recombination closes back to Planck — the
    structural transcend in the typeclass sense, NOT a physical claim
    that the universe loops. The typeclass cyclicity axiom requires only
    no-fixed-points on a finite type. -/
def next : CosmoPhase → CosmoPhase
  | .Planck          => .GUT
  | .GUT             => .Electroweak
  | .Electroweak     => .Quark
  | .Quark           => .Hadron
  | .Hadron          => .Nucleosynthesis
  | .Nucleosynthesis => .Recombination
  | .Recombination   => .Planck

/-- Segment assignment: the Z/3Z quotient.
    0 = PRE-BARYON, 1 = BARYON-FORMATION, 2 = STRUCTURE.

    The 3-3-1 partition groups phases by physical regime:
    pre-electroweak-breaking, matter formation, and photon-decoupled
    structure formation. -/
def segment : CosmoPhase → Fin 3
  | .Planck | .GUT | .Electroweak                        => 0  -- PRE-BARYON
  | .Quark | .Hadron | .Nucleosynthesis                  => 1  -- BARYON-FORMATION
  | .Recombination                                       => 2  -- STRUCTURE

/-- Whether a position is a segment boundary (segment changes on next).
    Three boundaries: mi-fa (Electroweak→Quark), la-si
    (Nucleosynthesis→Recombination), si-do transcend
    (Recombination→Planck). -/
def isBoundary : CosmoPhase → Bool
  | .Electroweak     => true   -- mi-fa: PRE-BARYON → BARYON-FORMATION
  | .Nucleosynthesis => true   -- la-si: BARYON-FORMATION → STRUCTURE
  | .Recombination   => true   -- si-do: STRUCTURE → PRE-BARYON (transcend)
  | _                => false

/-- The three textbook symmetry-breaking events of the early-universe
    ladder, marked at the position carrying the symmetry-breaking commit.

    Critically, `isShock` is NOT a subset of `isBoundary` for the
    cosmological ladder — `GUT` is the strong-decoupling event but
    lives intra-segment 0 (GUT→Electroweak is NOT a segment boundary).
    This is the natural-substrate signal that distinguishes cosmology
    from designed-substrate instances; designed-substrate
    `OctaveStructure` instances all satisfy `isShock ⊆ isBoundary`. -/
def isShock : CosmoPhase → Bool
  | .GUT             => true   -- Strong-decoupling at GUT scale (intra-segment 0)
  | .Electroweak     => true   -- EW symmetry breaking (mi-fa, segment 0→1)
  | .Nucleosynthesis => true   -- BBN transit (la-si, segment 1→2)
  | _                => false

end CosmoPhase

/-- The three canonical symmetry-breaking event types of the standard
    early-universe ladder. -/
inductive SymmetryBreakingEvent where
  | StrongDecoupling     -- GUT — gauge break: SU(5)/SO(10) → SU(3)×SU(2)×U(1)
  | EWSymmetryBreaking   -- Electroweak — Higgs VEV; W/Z gain mass
  | BBNTransit           -- Nucleosynthesis — BBN end / radiation-matter transit
  deriving DecidableEq, Repr, BEq

namespace CosmoPhase

/-- Map each shock position to its textbook symmetry-breaking event. -/
def symmetryEvent : CosmoPhase → Option SymmetryBreakingEvent
  | .GUT             => some .StrongDecoupling
  | .Electroweak     => some .EWSymmetryBreaking
  | .Nucleosynthesis => some .BBNTransit
  | _                => none

end CosmoPhase

-- ═══════════════════════════════════════════════════
-- BASIC STRUCTURAL THEOREMS (CE1–CE6)
-- ═══════════════════════════════════════════════════

/-- CE1: No fixed points — the successor always advances. -/
theorem ce_next_ne_self (p : CosmoPhase) : p.next ≠ p := by
  cases p <;> simp [CosmoPhase.next]

/-- CE2: Seven applications of next return to the original phase.
    The cosmological ladder is a structural 7-cycle. -/
theorem ce_transcend_7_eq_id (p : CosmoPhase) :
    p.next.next.next.next.next.next.next = p := by
  cases p <;> rfl

/-- CE3: Exactly 3 segment boundaries. -/
theorem ce_exactly_three_boundaries :
    (Finset.univ.filter (fun p : CosmoPhase => p.isBoundary)).card = 3 := by
  decide

/-- CE4: Exactly 3 active shocks (the three textbook symmetry-breaking
    events). -/
theorem ce_exactly_three_shocks :
    (Finset.univ.filter (fun p : CosmoPhase => p.isShock)).card = 3 := by
  decide

/-- CE5: Boundary ↔ segment change (the boundary predicate agrees
    exactly with "the segment changes on next" — what is notable here
    is that `isShock` does NOT coincide with this predicate, see CE10). -/
theorem ce_boundary_iff_segment_change (p : CosmoPhase) :
    p.isBoundary = true ↔ p.segment ≠ p.next.segment := by
  cases p <;>
    simp [CosmoPhase.isBoundary, CosmoPhase.segment, CosmoPhase.next]

/-- CE6: 2 of the 3 segment-boundaries are also shocks (Electroweak
    mi-fa, Nucleosynthesis la-si). The remaining segment-boundary is the
    Recombination si-do transcend, which is the regenerative cycle close
    — not an active shock. -/
theorem ce_two_boundaries_are_shocks :
    (Finset.univ.filter
      (fun p : CosmoPhase => p.isBoundary = true ∧ p.isShock = true)).card = 2 := by
  decide

-- ═══════════════════════════════════════════════════
-- OCTAVESTRUCTURE INSTANCE (CE7)
-- ═══════════════════════════════════════════════════

/-- CE7: **CosmoPhase is an `OctaveStructure` instance.**

    The algebra-class labelling carries 5 distinct `(id, tag)` pairs
    over 7 positions, with the matter-formation class `(id=3,
    tag="TransientToDurableTransition")` having cardinality 3 — the
    three matter-formation phases (Quark, Hadron, Nucleosynthesis) all
    share it.

    The tag strings are fixed descriptive names; the labelling is a
    modeling choice (see the file header). -/
instance : OctaveStructure CosmoPhase where
  next := CosmoPhase.next
  segment := CosmoPhase.segment
  algebraClass := fun p => match p with
    | .Planck          => ⟨0, "StructuredAbsenceInference"⟩    -- pre-decoupling era
    | .GUT             => ⟨1, "SoftToBindingTransition"⟩       -- gravity decoupled
    | .Electroweak     => ⟨2, "BoundaryPredicate"⟩             -- EW intact, awaits breaking
    | .Quark           => ⟨3, "TransientToDurableTransition"⟩  -- free quarks
    | .Hadron          => ⟨3, "TransientToDurableTransition"⟩  -- confined hadrons
    | .Nucleosynthesis => ⟨3, "TransientToDurableTransition"⟩  -- light-nuclei BBN (la-si)
    | .Recombination   => ⟨4, "ResultAsRowColumnInput"⟩        -- atoms; photons decouple
  next_ne_self := ce_next_ne_self
  segment_surjective := by
    intro s; fin_cases s
    · exact ⟨.Planck, rfl⟩
    · exact ⟨.Quark, rfl⟩
    · exact ⟨.Recombination, rfl⟩

/-- CE8: CosmoPhase self-product has exactly 9 regions
    (inherits from `generic_nine_regions`). -/
theorem ce_nine_regions :
    (Finset.image (fun c : CosmoPhase × CosmoPhase =>
      OctaveStructure.region c) Finset.univ).card = 9 := by
  decide

-- ═══════════════════════════════════════════════════
-- NATURAL-CLASS algebraClass THEOREMS (CE9a–CE9d)
-- ═══════════════════════════════════════════════════

/-- CE9a: **CosmoPhase has exactly 5 algebra-class transitions.**

    Counted positions where the algebra-class label changes on next:
    `Planck→GUT (id 0→1)`, `GUT→Electroweak (1→2)`,
    `Electroweak→Quark (2→3)`, `Nucleosynthesis→Recombination (3→4)`,
    `Recombination→Planck (4→0)`.

    The `Quark→Hadron` and `Hadron→Nucleosynthesis` transitions are
    NOT class-transitions — all three positions share the
    matter-formation class `(id=3, tag="TransientToDurableTransition")`,
    of cardinality 3.

    Two of the five class-transitions live INSIDE segment 0
    (Planck→GUT for gravity-decoupling, GUT→Electroweak for
    strong-decoupling). Three coincide with segment-boundaries
    (mi-fa Electroweak→Quark, la-si Nucleosynthesis→Recombination,
    si-do Recombination→Planck). -/
theorem ce_isClassTransition_count :
    (Finset.univ.filter
      (fun p : CosmoPhase => OctaveStructure.isClassTransition p)).card = 5 := by
  decide

/-- CE9b: **CosmoPhase exhibits exactly 5 distinct algebra-class tags.**

    Companion to CE9a. The 5 distinct `tag` strings are
    `"StructuredAbsenceInference"` (Planck), `"SoftToBindingTransition"`
    (GUT), `"BoundaryPredicate"` (Electroweak),
    `"TransientToDurableTransition"` (Quark, Hadron, Nucleosynthesis —
    cardinality 3 — the three matter-formation phases), and
    `"ResultAsRowColumnInput"` (Recombination). -/
theorem ce_distinct_tags_count :
    (Finset.image (fun p : CosmoPhase =>
      (OctaveStructure.algebraClass p).tag) Finset.univ).card = 5 := by
  decide

/-- CE9c: **CosmoPhase per-instance `isShock` ⊆ `isClassTransition`.**

    All three active shocks (GUT, Electroweak, Nucleosynthesis) have
    successors with different algebra-class. Proved directly via
    `decide` rather than via the typeclass-level
    `isShock_implies_isClassTransition_designed` lemma, because
    cosmology's non-trivial `algebraClass` does NOT satisfy that
    lemma's `algebraClass ≡ segment` compatibility hypothesis. -/
theorem ce_isShock_implies_isClassTransition (p : CosmoPhase) :
    p.isShock = true → OctaveStructure.isClassTransition p = true := by
  cases p <;> decide

/-- CE9d: **Exactly 2 intra-segment class-transitions.**

    The intra-segment class-transitions are `Planck` (Planck→GUT,
    intra-segment 0; gravity-decoupling) and `GUT` (GUT→Electroweak,
    intra-segment 0; strong-decoupling). Both live in segment 0 (the
    pre-baryon era), making segment 0 the algebra-class-rich segment of
    this encoding. -/
theorem ce_two_intra_segment_class_transitions :
    (Finset.univ.filter (fun p : CosmoPhase =>
      OctaveStructure.isClassTransition p = true ∧ p.isBoundary = false)).card = 2 := by
  decide

-- ═══════════════════════════════════════════════════
-- CE10–CE13 — THE NATURAL-SUBSTRATE SIGNAL
-- ═══════════════════════════════════════════════════

/-- CE10: **The natural-substrate signal — `isShock` ⊄ `isBoundary`.**

    Witness: `GUT` is a textbook symmetry-breaking event
    (`isShock = true`, strong-decoupling at GUT scale) but is NOT a
    segment boundary (`isBoundary = false`, GUT→Electroweak is
    intra-segment-0).

    An analogous intra-segment shock appears in encodings of other
    natural processes — e.g. the eukaryotic cell cycle, where the G1/S
    restriction point fires inside interphase. `OctaveStructure`
    instances modeling designed processes all satisfy
    `isShock ⊆ isBoundary`; this encoding violates that inclusion at
    the GUT-scale strong-decoupling. -/
theorem ce_shock_not_subset_boundary :
    ∃ p : CosmoPhase, p.isShock = true ∧ p.isBoundary = false := by
  refine ⟨.GUT, ?_, ?_⟩ <;> decide

/-- CE11: **Exactly 1 of the 3 shocks lives intra-segment.**

    The intra-segment shock is `GUT` (strong-decoupling, intra-segment 0).
    The other 2 shocks (`Electroweak` mi-fa and `Nucleosynthesis` la-si)
    coincide with segment-boundaries. The 1/3 intra-segment fraction is
    the natural-substrate signal of this encoding — instances modeling
    designed processes have 0/n intra-segment shocks. -/
theorem ce_one_intra_segment_shock :
    (Finset.univ.filter
      (fun p : CosmoPhase => p.isShock = true ∧ p.isBoundary = false)).card = 1 := by
  decide

/-- CE12: **Symmetry-breaking events map 1-to-1 to `isShock` positions.**

    `symmetryEvent p` is `some _` iff `p` is an active shock; the three
    symmetry-breaking event types correspond to the three shock
    positions (StrongDecoupling↔GUT, EWSymmetryBreaking↔Electroweak,
    BBNTransit↔Nucleosynthesis). -/
theorem ce_symmetry_iff_shock (p : CosmoPhase) :
    (CosmoPhase.symmetryEvent p).isSome = true ↔ p.isShock = true := by
  cases p <;> decide

/-- CE13: Exactly 3 textbook symmetry-breaking events. -/
theorem ce_exactly_three_symmetry_events :
    (Finset.univ.filter (fun p : CosmoPhase =>
      (CosmoPhase.symmetryEvent p).isSome)).card = 3 := by
  decide

-- ═══════════════════════════════════════════════════
-- CE14–CE15 — MI-FA AND LA-SI SHOCK WITNESSES
-- ═══════════════════════════════════════════════════

/-- CE14: **The mi-fa shock witness.** The mi-fa shock is the position
    whose successor crosses segment 0→1. For the cosmological ladder:
    Electroweak → Quark. The shock-carrying position has segment 0;
    its successor has segment 1. -/
theorem ce_mifa_shock_witness :
    CosmoPhase.isShock .Electroweak = true ∧
    CosmoPhase.segment .Electroweak = 0 ∧
    CosmoPhase.segment (CosmoPhase.next .Electroweak) = 1 := by
  exact ⟨rfl, rfl, rfl⟩

/-- CE15: **The la-si shock witness.**
    Nucleosynthesis → Recombination crosses segment 1→2. -/
theorem ce_lasi_shock_witness :
    CosmoPhase.isShock .Nucleosynthesis = true ∧
    CosmoPhase.segment .Nucleosynthesis = 1 ∧
    CosmoPhase.segment (CosmoPhase.next .Nucleosynthesis) = 2 := by
  exact ⟨rfl, rfl, rfl⟩

-- ═══════════════════════════════════════════════════
-- PUNCHLINES
-- ═══════════════════════════════════════════════════

/-- CE16: **COSMOLOGICAL EPOCHS OCTAVE PUNCHLINE.**

    The standard early-universe ladder is an OctaveStructure instance.
    7 phases, 3-3-1 segment distribution, 3 active symmetry-breaking
    events, 3 segment boundaries, 5 distinct algebra-class tags. The EW
    symmetry breaking is the mi-fa shock; the BBN transit is the la-si
    shock. The strong-decoupling at GUT scale is an additional
    intra-segment shock — the natural-substrate signal. -/
theorem ce_octave_punchline :
    Fintype.card CosmoPhase = 7 ∧
    (Finset.univ.filter (fun p : CosmoPhase => p.isShock)).card = 3 ∧
    (Finset.univ.filter (fun p : CosmoPhase => p.isBoundary)).card = 3 ∧
    (Finset.image (fun p : CosmoPhase =>
      (OctaveStructure.algebraClass p).tag) Finset.univ).card = 5 := by
  exact ⟨by decide, by decide, by decide, by decide⟩

/-- CE17: **COMBINED STRUCTURAL SIGNATURE.**

    The encoding exhibits all three structural signals that, within
    this development, separate instances drawn from natural processes
    from those modeling designed processes:

    1. `algebraClass` is non-trivial (5 distinct ids, not 3≡segment).
    2. `isClassTransition` count exceeds the 3-boundary count (5
       transitions over 7 positions; 2 of them intra-segment 0).
    3. `isShock` is NOT a subset of `isBoundary` (1 of 3 shocks lives
       intra-segment — the strong-decoupling at GUT scale).

    As throughout, these are properties of the chosen encoding —
    counts, inclusions, and witnesses over a finite type — not
    physical claims. -/
theorem ce_natural_class_completeness :
    -- (1) Non-trivial algebraClass
    (Finset.image (fun p : CosmoPhase =>
      (OctaveStructure.algebraClass p).id) Finset.univ).card = 5 ∧
    -- (2) Class transitions exceed segment boundaries
    (Finset.univ.filter
      (fun p : CosmoPhase => OctaveStructure.isClassTransition p)).card >
    (Finset.univ.filter (fun p : CosmoPhase => p.isBoundary)).card ∧
    -- (3) isShock not subset of isBoundary (intra-segment shocks exist)
    (∃ p : CosmoPhase, p.isShock = true ∧ p.isBoundary = false) := by
  refine ⟨?_, ?_, ?_⟩
  · decide
  · decide
  · exact ⟨.GUT, by decide, by decide⟩

end CosmoEpochs

/-!
## Summary

**20 theorems proved. 0 sorry.**

`CosmoEpochs.CosmoPhase` — the standard early-universe ladder
`(Planck, GUT, Electroweak, Quark, Hadron, Nucleosynthesis, Recombination)`
— is an `OctaveStructure` under the encoding fixed in the file header:
segments by physical regime (3-3-1), shocks at the three textbook
symmetry-breaking events, and a 5-class algebra labelling.

**Key results:**

- `CE7` (instance)            : CosmoPhase is an OctaveStructure
- `CE1` (ce_next_ne_self)     : cyclic successor has no fixed points
- `CE2` (ce_transcend_7_eq_id): 7 applications return to origin
- `CE3–CE4`                   : 3 boundaries, 3 shocks
- `CE5`                       : boundary ↔ segment change
- `CE9a–CE9d`                 : 5 class transitions, 5 distinct tags,
                                isShock ⊆ isClassTransition,
                                2 intra-segment class transitions
- `CE10` (ce_shock_not_subset_boundary)
                              : **the natural-substrate signal** —
                                isShock NOT a subset of isBoundary
                                (GUT strong-decoupling intra-segment 0)
- `CE11`                      : exactly 1 of 3 shocks intra-segment
- `CE12`                      : symmetry events ↔ shocks bijection
- `CE13`                      : exactly 3 textbook symmetry-breaking events
- `CE14–CE15`                 : mi-fa and la-si shock witnesses
- `CE17` (ce_natural_class_completeness)
                              : combined structural signature

**What is and is not claimed:**

The proofs certify the shape of the encoded order structure — counts,
inclusions, and witnesses over a finite type — not the physics. The
choice of phases, segments, shock markers, and class labels is a stated
modeling choice. The cyclic close `Recombination → Planck` is a
structural device required by the typeclass; the companion file
`CosmoEpochsGradedCoverNegative` proves that the physical epoch order
admits no time-respecting cyclic close, so the cyclic reading is
imposed rather than derived.
-/
