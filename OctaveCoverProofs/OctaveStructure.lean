import OctaveCoverProofs.NarrativeOctave
import Mathlib.Tactic

/-!
# OctaveStructure — The Abstract Octave Algebra

## The Unification

`Layer.lean` defines 9 positions with 3 shocks.
`NarrativeOctave.lean` defines 7 positions with 3 boundaries.
Both satisfy: `boundary p ↔ segment p ≠ segment (next p)`.

This module captures the ABSTRACT STRUCTURE they share: an octave is a
finite cyclic type with a surjective segment map to Fin 3 such that
segment changes coincide with boundary points.

Both Layer and NarrativePos are instances. The product of any two
octave structures produces a 9-region grid — proved ONCE, inherited
by all instances.

## Why This Matters

The 9-region grid is not asserted instance-by-instance: any type
satisfying the octave axioms produces the same product topology when
crossed with itself (or with any other octave structure). The
decomposition holds because the algebra forces it, not because a
particular instance was checked.

These theorems certify properties of the encoded structures themselves,
not any empirical claim about systems the structures may be used to model.
-/

-- ═══════════════════════════════════════════════════
-- ALGEBRA-CLASS LABELS
-- ═══════════════════════════════════════════════════

/-- Identifier for the algebraic-relation-class that governs an
    octave position.

    `id` carries the semantic load: two positions are in the same
    algebra-class iff they share `id`. `tag` carries an optional
    self-documenting name for the class (e.g. `"CoordAssemble"`,
    `"BoundaryPredicate"`); it may be left empty.

    Designed instances — those whose class structure is chosen by
    construction, such as `NarrativePos` and `Layer` below — set `id`
    1-to-1 with `segment` and use `tag := ""` (the algebra-class is
    fully recoverable from `segment`).

    Natural-class instances — those modeling a pre-existing
    classification, e.g. the phases of the cell cycle or the blocks of
    the periodic table — may use richer `id` and `tag` values that
    distinguish multiple algebra-classes within a single segment,
    including classes whose cardinality exceeds 1 inside one segment. -/
structure AlgebraClassLabel where
  id : Nat
  tag : String
  deriving DecidableEq, Repr

/-- Two `AlgebraClassLabel`s are equal iff both their `id` and `tag`
    fields are equal. Provides an `apply`-style handle for proofs that
    construct a label-equality from per-field equalities. -/
@[ext] theorem AlgebraClassLabel.ext_id_tag
    {a b : AlgebraClassLabel}
    (h_id : a.id = b.id) (h_tag : a.tag = b.tag) : a = b := by
  cases a; cases b; simp_all

-- ═══════════════════════════════════════════════════
-- THE ABSTRACT OCTAVE STRUCTURE
-- ═══════════════════════════════════════════════════

/-- An octave structure on a finite type α.

    The minimal axioms:
    1. A cyclic successor (next) with no fixed points
    2. A segment map to Fin 3 (the Z/3Z quotient)
    3. Surjectivity: all 3 segments are inhabited
    4. An algebraClass label per position (an identifier for the
       algebraic-relation-class governing that position)

    The boundary invariant `isBoundary p ↔ segment p ≠ segment (next p)`
    is automatic from the derived `isBoundary` definition.

    The class-transition predicate `isClassTransition p ↔
    algebraClass p ≠ algebraClass (next p)` captures the notion of an
    algebra-class shift along the cycle.

    For designed instances `algebraClass ≡ segment`; for natural-class
    instances `algebraClass` may distinguish multiple classes per
    segment. From these, the 9-region product decomposition follows
    automatically. -/
class OctaveStructure (α : Type) [Fintype α] [DecidableEq α] where
  /-- Cyclic successor: generates the full cycle. -/
  next : α → α
  /-- Segment assignment: the Z/3Z quotient. -/
  segment : α → Fin 3
  /-- Algebra-class label per position. Designed instances set this
      1-to-1 with `segment`; natural-class instances may carry richer labels. -/
  algebraClass : α → AlgebraClassLabel
  /-- No fixed points: the successor always advances. -/
  next_ne_self : ∀ p : α, next p ≠ p
  /-- All segments are inhabited. -/
  segment_surjective : ∀ s : Fin 3, ∃ p : α, segment p = s

namespace OctaveStructure

variable {α : Type} [Fintype α] [DecidableEq α] [OctaveStructure α]

/-- Derived: a boundary is where the segment changes on next.
    Includes the transcend (cycle close, segment 2 → segment 0). -/
def isBoundary (p : α) : Bool :=
  decide (segment p ≠ segment (next p))

/-- Derived: a class transition is where the algebra-class changes on next.
    For designed instances with `algebraClass ≡ segment`, this collapses
    to `isBoundary` (see `isClassTransition_eq_isBoundary_when_class_eq_segment`).
    For natural-class instances with richer algebra-class labels, the
    predicate can fire intra-segment (e.g. cell-cycle G1/S Restriction
    Point, periodic-table s→p block transition). -/
def isClassTransition (p : α) : Bool :=
  decide (algebraClass p ≠ algebraClass (next p))

/-- The region of a cell in the product grid. -/
def region (c : α × α) : Fin 3 × Fin 3 :=
  (segment c.1, segment c.2)

/-- Compatibility: when `algebraClass ≡ segment` (the designed-instance
    case), `isClassTransition` collapses exactly to the boundary predicate.

    Two hypotheses are needed because `AlgebraClassLabel` carries both
    `id` and `tag`:

    - `h_id` ties the algebra-class id to the segment value; enough to
      drive class-transition from a segment-change in the backward
      direction.
    - `h_tag` says tags are pairwise constant across positions; trivially
      discharged at any designed-instance call site by `fun _ _ => rfl`
      since designed instances use `tag := ""`. Required for the
      forward direction so that label-equality follows from id-equality.

    Under both, all 3 boundaries are class transitions — including the
    transcend. The strictly stricter per-instance `isShock` predicate
    (excluding the transcend) is captured by
    `isShock_implies_isClassTransition_designed`. -/
theorem isClassTransition_eq_isBoundary_when_class_eq_segment
    (h_id : ∀ p : α, (algebraClass p).id = (segment p).val)
    (h_tag : ∀ p q : α, (algebraClass p).tag = (algebraClass q).tag) :
    ∀ p : α, isClassTransition p = true ↔ segment p ≠ segment (next p) := by
  intro p
  simp only [isClassTransition, decide_eq_true_eq, ne_eq]
  refine Iff.intro ?_ ?_
  · intro hne hseg
    apply hne
    apply AlgebraClassLabel.ext_id_tag
    · rw [h_id, h_id, hseg]
    · exact h_tag p (next p)
  · intro hne hcls
    apply hne
    apply Fin.ext
    rw [← h_id, ← h_id, hcls]

/-- Per-instance shock predicates that respect the boundary invariant
    are always subsets of `isClassTransition` under the
    designed-instance compatibility hypotheses.

    The distinction encoded by a per-instance `isShock` predicate
    (which may exclude the cycle-closing transcend) is finer than the
    algebra-class transition concept — but every such shock IS an
    algebra-class transition. This lemma documents that subset relation
    for instance authors: their `isShock` must remain ⊆ class
    transitions.

    Natural-class instances where `algebraClass` does not satisfy
    `h_id`/`h_tag` should prove their own subset lemma directly via
    `decide` against their concrete map. -/
theorem isShock_implies_isClassTransition_designed
    (h_id : ∀ p : α, (algebraClass p).id = (segment p).val)
    (h_tag : ∀ p q : α, (algebraClass p).tag = (algebraClass q).tag)
    (isShockPI : α → Bool)
    (h_shock_subset_boundary :
      ∀ p : α, isShockPI p = true → segment p ≠ segment (next p)) :
    ∀ p : α, isShockPI p = true → isClassTransition p = true := by
  intro p hpi
  rw [isClassTransition_eq_isBoundary_when_class_eq_segment h_id h_tag]
  exact h_shock_subset_boundary p hpi

end OctaveStructure

-- ═══════════════════════════════════════════════════
-- INSTANCE: NarrativePos
-- ═══════════════════════════════════════════════════

instance : OctaveStructure NarrativePos where
  next := NarrativePos.next
  segment := NarrativePos.segment
  algebraClass := fun p => ⟨(NarrativePos.segment p).val, ""⟩
  next_ne_self := narrative_next_ne_self
  segment_surjective := by
    intro s
    fin_cases s
    · exact ⟨.Do, rfl⟩
    · exact ⟨.Fa, rfl⟩
    · exact ⟨.Si, rfl⟩

-- ═══════════════════════════════════════════════════
-- INSTANCE: Layer
-- ═══════════════════════════════════════════════════

/-- Layer.triad as Fin 3 for the typeclass interface. -/
def Layer.segmentFin3 (l : Layer) : Fin 3 :=
  match l.triad with
  | .first  => 0
  | .second => 1
  | .third  => 2

instance : OctaveStructure Layer where
  next := Layer.next
  segment := Layer.segmentFin3
  algebraClass := fun l => ⟨(Layer.segmentFin3 l).val, ""⟩
  next_ne_self := next_ne_self
  segment_surjective := by
    intro s
    fin_cases s
    · exact ⟨.L0, by decide⟩
    · exact ⟨.L3, by decide⟩
    · exact ⟨.L6, by decide⟩

-- ═══════════════════════════════════════════════════
-- THE GENERIC 9-REGION THEOREM
-- ═══════════════════════════════════════════════════

/-- For ANY octave structure α, the product α × α has exactly 9 regions.

    Proof: segment is surjective onto Fin 3 (axiom), so (segment, segment)
    is surjective onto Fin 3 × Fin 3. The image of a surjective function
    on Finset.univ equals Finset.univ, which has card 9. -/
theorem generic_nine_regions (α : Type) [Fintype α] [DecidableEq α]
    [OctaveStructure α] :
    (Finset.image (fun c : α × α => OctaveStructure.region c)
      Finset.univ).card = 9 := by
  convert Finset.card_univ
  ext ⟨x, y⟩; simp [OctaveStructure.region]
  exact ⟨‹OctaveStructure α›.segment_surjective x, ‹OctaveStructure α›.segment_surjective y⟩

/-- For NarrativePos specifically, 9 regions — a concrete check of the
    generic theorem via the typeclass interface. -/
theorem narrative_nine_regions_via_typeclass :
    (Finset.image (fun c : NarrativePos × NarrativePos =>
      OctaveStructure.region c) Finset.univ).card = 9 := by
  decide

/-- For Layer specifically, 9 regions via the typeclass interface. -/
theorem layer_nine_regions_via_typeclass :
    (Finset.image (fun c : Layer × Layer =>
      OctaveStructure.region c) Finset.univ).card = 9 := by
  decide

-- ═══════════════════════════════════════════════════
-- CROSS-TYPE PRODUCTS
-- ═══════════════════════════════════════════════════

/-- The mixed product NarrativePos × Layer also has 9 regions.
    This is the narrative-position × layer grid. -/
def mixedRegion (c : NarrativePos × Layer) : Fin 3 × Fin 3 :=
  (NarrativePos.segment c.1, Layer.segmentFin3 c.2)

theorem mixed_nine_regions :
    (Finset.image mixedRegion Finset.univ).card = 9 := by
  decide

-- ═══════════════════════════════════════════════════
-- THE BOUNDARY-SHOCK SPECTRUM
-- ═══════════════════════════════════════════════════

/-- In Layer, every boundary is a shock (3/3). -/
theorem layer_all_boundaries_are_shocks :
    ∀ l : Layer, Layer.segmentFin3 l ≠ Layer.segmentFin3 l.next →
      l.isShockPoint = true := by
  intro l
  cases l <;> simp [Layer.segmentFin3, Layer.triad, Layer.next, Layer.isShockPoint]

/-- In NarrativePos, not all boundaries are shocks (2/3).
    Si is a boundary (segment changes) but not a shock (it's the transcend). -/
theorem narrative_has_non_shock_boundary :
    ∃ p : NarrativePos,
      NarrativePos.segment p ≠ NarrativePos.segment p.next ∧
      p.isShock = false := by
  exact ⟨.Si, by decide, by decide⟩

/-- The boundary/shock ratio characterizes the octave type:
    - Layer: 3 boundaries, 3 shocks → ratio 1.0 (fully stressed)
    - NarrativePos: 3 boundaries, 2 shocks → ratio 0.67 (one transcend) -/
theorem layer_shock_ratio :
    (Finset.univ.filter (fun l : Layer => l.isShockPoint)).card = 3 := by
  decide

theorem narrative_shock_ratio :
    (Finset.univ.filter (fun p : NarrativePos => p.isShock)).card = 2 := by
  decide

theorem narrative_boundary_ratio :
    (Finset.univ.filter (fun p : NarrativePos =>
      NarrativePos.segment p ≠ NarrativePos.segment p.next)).card = 3 := by
  decide
