import OctaveCoverProofs.Layer
import Mathlib.Data.ZMod.Basic

/-!
# TwoCoordinates — The Two Coordinates of the 9-Layer Cycle

## I — From Behavior to Algebra

The `Layer` module proves that the 9 layers cycle (`transcend⁹ = id`) and
that shock points sit at triad boundaries. These are behavioral facts —
WHAT happens. This module adds the algebraic WHY: `Layer` IS Z/9Z, the
cyclic group of order 9. The successor function is the generator (+1).
Every theorem in the `Layer` module is a shadow of this group structure.

## II — The Two Decompositions

The nine layers admit two natural 3-fold decompositions:

- **Role** (`index mod 3`): Initiator (0), Developer (1), Completer (2).
  This IS a group homomorphism Z/9Z → Z/3Z — it respects the successor.
- **Octave** (`index ÷ 3`): Material (0), Structural (1), Integrative (2).
  This is NOT a group homomorphism — it is purely structural.

The shock points are exactly the Completers (role = 2). Advancing past a
Completer necessarily changes the Octave coordinate. The asymmetry —
one coordinate is algebraic, the other merely structural — is WHERE the
shock energy lives. The group knows about roles; it does not know about octaves.

## III — The Cylinder

The (role, octave) pair identifies each layer uniquely — a bijection from
Z/9Z to a 3×3 grid:

       Role 0       Role 1       Role 2 (shock)
      (initiator)  (developer)  (completer)
    ┌────────────┬────────────┬────────────┐
  0 │ L0         │ L1         │ L2      ───┤
    ├────────────┼────────────┼────────────┤
  1 │ L3         │ L4         │ L5      ───┤ shock
    ├────────────┼────────────┼────────────┤
  2 │ L6         │ L7         │ L8      ───┘→ L0
    └────────────┴────────────┴────────────┘

The generator winds through this grid left-to-right, top-to-bottom. Each time
it reaches the right edge (role 2), the next step MUST cross to the next
row (octave). Z/9Z ≇ Z/3Z × Z/3Z — the cyclic structure cannot be decomposed
into independent role and octave components. The octave bands are not
independent: they are wound together in a single spiral.

These theorems certify the encoded combinatorial structure — nothing more.
-/

-- ═══════════════════════════════════════════════════════
-- INFRASTRUCTURE
-- ═══════════════════════════════════════════════════════

/-- Layer is finite (9 elements). Enables `decide`/`decide`
    for universally quantified propositions over Layer. -/
instance : Fintype Layer where
  elems := ⟨[Layer.L0, Layer.L1, Layer.L2, Layer.L3, Layer.L4,
              Layer.L5, Layer.L6, Layer.L7, Layer.L8], by decide⟩
  complete l := by cases l <;> decide

namespace Layer

-- ═══════════════════════════════════════════════════════
-- SECTION I: THE ISOMORPHISM — Layer IS Z/9Z
-- ═══════════════════════════════════════════════════════

/-- Encode a layer as its element of Z/9Z. -/
def toZMod : Layer → ZMod 9
  | .L0 => 0 | .L1 => 1 | .L2 => 2
  | .L3 => 3 | .L4 => 4 | .L5 => 5
  | .L6 => 6 | .L7 => 7 | .L8 => 8

/-- Decode an element of Z/9Z back to a layer. -/
def ofZMod (x : ZMod 9) : Layer :=
  match x.val with
  | 0 => .L0 | 1 => .L1 | 2 => .L2
  | 3 => .L3 | 4 => .L4 | 5 => .L5
  | 6 => .L6 | 7 => .L7 | 8 => .L8
  | _ => .L0  -- unreachable for ZMod 9

/-- Round-trip: decode after encode is identity. -/
theorem ofZMod_toZMod (l : Layer) : ofZMod (toZMod l) = l := by
  cases l <;> decide

/-- Round-trip: encode after decode is identity. -/
theorem toZMod_ofZMod (x : ZMod 9) : toZMod (ofZMod x) = x := by
  fin_cases x <;> decide

/-- The equivalence between Layer and Z/9Z. -/
def equivZMod9 : Layer ≃ ZMod 9 where
  toFun := toZMod
  invFun := ofZMod
  left_inv := ofZMod_toZMod
  right_inv := toZMod_ofZMod

/-- THE CORRESPONDENCE: Layer.next IS (+1) in Z/9Z.
    The cyclic successor is the group generator's action. -/
theorem next_is_succ (l : Layer) :
    (next l).toZMod = l.toZMod + 1 := by
  cases l <;> decide

/-- Encoding preserves the existing index: toZMod.val = index. -/
theorem toZMod_val_eq_index (l : Layer) :
    (toZMod l).val = l.index := by
  cases l <;> decide

-- ═══════════════════════════════════════════════════════
-- SECTION II: THE TWO COORDINATES
-- ═══════════════════════════════════════════════════════

/-- Role within an octave: the algebraic coordinate (index mod 3).
    0 = Initiator, 1 = Developer, 2 = Completer (shock point).
    This projection respects the group operation. -/
def role : Layer → Fin 3
  | .L0 | .L3 | .L6 => 0  -- Initiator
  | .L1 | .L4 | .L7 => 1  -- Developer
  | .L2 | .L5 | .L8 => 2  -- Completer

/-- Octave: the structural coordinate (index ÷ 3).
    0 = Material (L0-L2), 1 = Structural (L3-L5), 2 = Integrative (L6-L8).
    This projection does NOT respect the group operation. -/
def octave : Layer → Fin 3
  | .L0 | .L1 | .L2 => 0  -- Material
  | .L3 | .L4 | .L5 => 1  -- Structural
  | .L6 | .L7 | .L8 => 2  -- Integrative

/-- Shock points are exactly the Completers: role = 2. -/
theorem shock_iff_completer (l : Layer) :
    l.isShockPoint = true ↔ (role l).val = 2 := by
  cases l <;> decide

/-- Role advances cyclically with next: role(next l) = (role l + 1) mod 3.
    This is the homomorphism property — the algebraic coordinate tracks the group. -/
theorem role_of_next (l : Layer) :
    (role (next l)).val = ((role l).val + 1) % 3 := by
  cases l <;> decide

/-- Octave 0 = first triad (Material). -/
theorem octave_zero_iff_first (l : Layer) :
    (octave l).val = 0 ↔ l.triad = .first := by
  cases l <;> decide

/-- Octave 1 = second triad (Structural). -/
theorem octave_one_iff_second (l : Layer) :
    (octave l).val = 1 ↔ l.triad = .second := by
  cases l <;> decide

/-- Octave 2 = third triad (Integrative). -/
theorem octave_two_iff_third (l : Layer) :
    (octave l).val = 2 ↔ l.triad = .third := by
  cases l <;> decide

/-- THE TWO COORDINATES ARE JOINTLY INJECTIVE:
    (role, octave) uniquely identifies every layer.
    The 3×3 grid has no collisions. -/
theorem two_coords_injective : ∀ l₁ l₂ : Layer,
    role l₁ = role l₂ → octave l₁ = octave l₂ → l₁ = l₂ := by
  decide

-- ═══════════════════════════════════════════════════════
-- SECTION III: THE NON-DECOMPOSABILITY
-- ═══════════════════════════════════════════════════════

/-- Crossing a shock point changes the octave.
    At role = 2, the next step jumps to the next row of the 3×3 grid. -/
theorem shock_changes_octave : ∀ l : Layer,
    l.isShockPoint = true → octave l ≠ octave (next l) := by
  decide

/-- Non-shock transitions preserve the octave.
    Within a row of the 3×3 grid, movement is purely horizontal. -/
theorem non_shock_preserves_octave : ∀ l : Layer,
    l.isShockPoint = false → octave l = octave (next l) := by
  decide

/-- THE NON-DECOMPOSABILITY THEOREM:
    The layer cycle has order 9, not 3. Three steps do NOT return to start.
    This proves Z/9Z ≇ Z/3Z × Z/3Z (the latter has exponent 3).
    The octaves are wound together in a single spiral, not stacked. -/
theorem cycle_not_exponent_three : ∃ l : Layer, l.iterate 3 ≠ l :=
  ⟨.L0, by decide⟩

/-- No period shorter than 9 closes the cycle for ALL layers.
    Together with transcend_9_eq_id, this establishes |Z/9Z| = 9. -/
theorem no_shorter_period :
    (∃ l : Layer, l.iterate 1 ≠ l) ∧
    (∃ l : Layer, l.iterate 2 ≠ l) ∧
    (∃ l : Layer, l.iterate 3 ≠ l) ∧
    (∃ l : Layer, l.iterate 4 ≠ l) ∧
    (∃ l : Layer, l.iterate 5 ≠ l) ∧
    (∃ l : Layer, l.iterate 6 ≠ l) ∧
    (∃ l : Layer, l.iterate 7 ≠ l) ∧
    (∃ l : Layer, l.iterate 8 ≠ l) :=
  ⟨⟨.L0, by decide⟩, ⟨.L0, by decide⟩,
   ⟨.L0, by decide⟩, ⟨.L0, by decide⟩,
   ⟨.L0, by decide⟩, ⟨.L0, by decide⟩,
   ⟨.L0, by decide⟩, ⟨.L0, by decide⟩⟩

/-- The generator L0 visits all 9 layers before returning.
    The orbit of +1 starting at 0 is the entire group. -/
theorem generator_orbit_is_full :
    ∀ l : Layer, ∃ k : Fin 9, L0.iterate k.val = l := by
  intro l; cases l
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨4, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨6, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨8, rfl⟩

end Layer
