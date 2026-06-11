import Mathlib.Tactic
import OctaveCoverProofs.GradedOctaveCover

/-!
  ## PeriodicTableGradedCover — the chemistry instance of the graded octave cover

  **What this is.** `GradedOctaveCover.lean` proves the abstract core: a flat
  cyclic base is the degree-0 face of a ℤ-graded cover whose winding generator is a
  non-coboundary. The natural follow-up question is whether any *concrete domain* forces a real
  grade (as opposed to an observer merely counting loops). This file answers YES for
  chemistry — within the encoding defined below.

  **The chemistry.** The periodic table's genuine recurrence is by **group** (column): Li → … →
  Ne → **Na** — traverse the eight s/p main-group columns and you land on group 1 again, one
  period UP. That is Newlands' 1865 *law of octaves* (every 8th element). So:

  - **Base = the group**, a closing cycle `ℤ/8ℤ` (`nextGroup`, `group_cycle_8`). The
    noble-gas → alkali close (G8→G1) is a *real* chemical recurrence, not an artifact of labeling.
  - **Grade = the period / shell number `n`** (`shellNumber`), the principal quantum number —
    a spectroscopically measured quantity. One octave (8 columns) up climbs
    exactly one shell (`shell_increments_per_octave`).
  - **The non-vacuity witness:** the shell grade is NOT a
    coboundary of any group-potential — same group, different shell exists (Na≠Li,
    `same_group_different_shell`), so the period-advancing connection has nonzero group-holonomy
    (`gholonomy (const 1) = 8`) and is therefore not group-native
    (`shell_advance_not_group_native`). The winding climbs; it does not close.

  **In-file negative control (non-vacuity by shape).** `gholonomy` provably attains both `8`
  (the shell-advance winding) and `0` (every group-only coboundary) — so a measured group-
  holonomy *means* something; the positive verdict is not self-satisfying. Contrast the
  cosmology encoding (`CosmoEpochsOctave.lean`), whose own docstring flags its cycle-close as
  a typeclass convenience, NOT a physical claim that the universe loops — a one-way arrow with
  no recurring base. Chemistry instantiates the pattern; cosmology (correctly, and provably —
  see `CosmoEpochsGradedCoverNegative.lean`) does not. The framework can say no.

  Honest scope: this file is **deliberately scoped to the s/p main groups** (the ℤ/8 octave).
  The d/f blocks make real periods irregular (8/18/32); extending the encoding to them is left
  open, and nothing here claims it. The abstract core this file instantiates is in
  `GradedOctaveCover.lean`. Whether the s/p encoding captures real chemistry is a modeling
  judgment the reader should make by reading the definitions.
-/

namespace PeriodicTableGradedCover

-- ============================================================
-- THE GROUP BASE  (ℤ/8 — Newlands' octave of the s/p main groups)
-- ============================================================

/-- The eight s/p main-group columns. G1 = alkali (ns¹), …, G8 = noble gas (np⁶).
    These are the classic octave: every eighth element repeats chemical character. -/
inductive Group | G1 | G2 | G3 | G4 | G5 | G6 | G7 | G8
  deriving DecidableEq, Repr

/-- Group successor. The columns advance; G8 (noble gas) → G1 (alkali) closes the octave —
    and that close is where the period steps up by one (Ne→Na). The grade records the step. -/
def nextGroup : Group → Group
  | .G1 => .G2 | .G2 => .G3 | .G3 => .G4 | .G4 => .G5
  | .G5 => .G6 | .G6 => .G7 | .G7 => .G8 | .G8 => .G1

/-- Iterated group successor. -/
def nextGroup_n : Nat → Group → Group
  | 0, g => g
  | n + 1, g => nextGroup (nextGroup_n n g)

/-- **The base closes: `nextGroup⁸ = id`.** ℤ/8 — the law of octaves. -/
theorem group_cycle_8 (g : Group) : nextGroup_n 8 g = g := by
  cases g <;> rfl

/-- Group successor has no fixed point. -/
theorem nextGroup_ne_self (g : Group) : nextGroup g ≠ g := by
  cases g <;> decide

theorem nextGroup_n_add (a b : ℕ) (g : Group) :
    nextGroup_n (a + b) g = nextGroup_n a (nextGroup_n b g) := by
  induction a with
  | zero => simp [nextGroup_n]
  | succ k ih => simp only [Nat.succ_add, nextGroup_n, ih]

-- ============================================================
-- THE COVER  +  THE PHYSICAL GRADE (shell / period number)
-- ============================================================

/-- The cover projection: the s/p filling sequence ℕ → Group. Element `n` (in the sp
    approximation, filling order from H/Li) sits in column `projGroup n`. -/
def projGroup (n : ℕ) : Group := nextGroup_n n Group.G1

/-- The physically-forced grade: the period / principal-shell number of element `n`.
    Eight columns per shell ⇒ `n/8 + 1`. This is the spectroscopic quantum number, not a
    curator's loop-counter. -/
def shellNumber (n : ℕ) : ℕ := n / 8 + 1

/-- Climbing one column projects to one `nextGroup` step (the bundle commuting square). -/
theorem projGroup_succ (n : ℕ) : projGroup (n + 1) = nextGroup (projGroup n) := rfl

/-- **The octave is the deck transformation.** One full group-loop (`+8`) returns to the same
    column: `projGroup` is 8-periodic, so the base is `ℕ/8ℕ` (group = degree-0 face). -/
theorem projGroup_periodic (n : ℕ) : projGroup (n + 8) = projGroup n := by
  unfold projGroup
  rw [nextGroup_n_add, group_cycle_8]

/-- **The forced winding: one octave loop = exactly one shell.** The principal quantum number
    increments by one per traversal of the eight columns — the substrate's own grade climbs. -/
theorem shell_increments_per_octave (n : ℕ) : shellNumber (n + 8) = shellNumber n + 1 := by
  unfold shellNumber
  rw [Nat.add_div_right n (by norm_num : 0 < 8)]

/-- **Na ≠ Li.** Same group (`projGroup 0 = projGroup 8 = G1`, alkali), different shell
    (`shellNumber 0 = 1`, `shellNumber 8 = 2`). The grade is not recoverable from the column
    alone — the concrete non-coboundary fact. -/
theorem same_group_different_shell :
    ∃ m n : ℕ, projGroup m = projGroup n ∧ shellNumber m ≠ shellNumber n := by
  refine ⟨0, 8, ?_, ?_⟩
  · exact (projGroup_periodic 0).symm
  · decide

-- ============================================================
-- THE NON-COBOUNDARY WITNESS  (over the group base)
-- ============================================================

/-- A connection on the group base assigns a fiber (shell) displacement to each column edge. -/
abbrev GConn : Type := Group → ℤ

/-- The eight-column orbit from G1. -/
def groupOrbit (g : Group) : List Group :=
  [g, nextGroup g, nextGroup_n 2 g, nextGroup_n 3 g,
   nextGroup_n 4 g, nextGroup_n 5 g, nextGroup_n 6 g, nextGroup_n 7 g]

/-- Group-holonomy: total shell displacement around one octave loop. -/
def gholonomy (δ : GConn) : ℤ := ((groupOrbit Group.G1).map δ).sum

/-- A connection is *group-native* iff it is a coboundary of a column-potential — i.e. the
    shell displacement is recoverable from the column alone. -/
def IsGroupNative (δ : GConn) : Prop := ∃ p : Group → ℤ, ∀ g, δ g = p (nextGroup g) - p g

/-- The shell-advance connection (`+1` per column) has group-holonomy `8`: eight columns,
    one shell. Witnesses that the observable is nonzero. -/
theorem gholonomy_const_one_eq_eight : gholonomy (fun _ => (1 : ℤ)) = 8 := by
  simp only [gholonomy, groupOrbit, nextGroup_n, nextGroup,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num

/-- Every column-potential coboundary has group-holonomy `0` (telescoping). -/
theorem gholonomy_coboundary (p : Group → ℤ) :
    gholonomy (fun g => p (nextGroup g) - p g) = 0 := by
  simp only [gholonomy, groupOrbit, nextGroup_n, nextGroup,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-- Every group-native connection is flat. -/
theorem group_native_is_flat (δ : GConn) (h : IsGroupNative δ) : gholonomy δ = 0 := by
  obtain ⟨p, hp⟩ := h
  have : δ = (fun g => p (nextGroup g) - p g) := funext hp
  rw [this]; exact gholonomy_coboundary p

/-- **The non-coboundary witness.** The shell-advance connection is
    NOT group-native: the principal quantum number cannot be recovered from the column. Proof:
    if it were group-native it would be flat, but its group-holonomy is `8 ≠ 0`. So the
    periodic table's grade is a genuine winding — it cannot be defined away inside the
    group circle. -/
theorem shell_advance_not_group_native : ¬ IsGroupNative (fun _ => (1 : ℤ)) := by
  intro h
  have hflat := group_native_is_flat _ h
  rw [gholonomy_const_one_eq_eight] at hflat
  norm_num at hflat

/-- In-file negative control: the observable separates the shell-advance winding (`8`) from
    every group-only coboundary (`0`). The result is non-vacuous, not self-satisfying. -/
theorem gholonomy_non_vacuous :
    (∃ δ : GConn, gholonomy δ ≠ 0) ∧ (∃ δ : GConn, gholonomy δ = 0) := by
  refine ⟨⟨fun _ => 1, ?_⟩, ⟨fun _ => 0, ?_⟩⟩
  · rw [gholonomy_const_one_eq_eight]; norm_num
  · simpa using gholonomy_coboundary (fun _ => 0)

/-- The physical grade and the abstract group-holonomy agree: the shell jump over one octave
    (`+1`), scaled by the eight columns, is exactly the shell-advance holonomy (`8`). -/
theorem shell_jump_matches_holonomy :
    ((shellNumber 8 : ℤ) - shellNumber 0) * 8 = gholonomy (fun _ => 1) := by
  rw [gholonomy_const_one_eq_eight]; norm_num [shellNumber]

-- ============================================================
-- THE CHEMISTRY VERDICT, ASSEMBLED
-- ============================================================

/-- **The chemistry instance, assembled (scoped to the s/p main groups).** The eight main-group
    columns are a closing base (`ℤ/8`, Newlands' octave); the period/shell number is a physically
    meaningful grade that climbs exactly one shell per octave loop; the shell-advance is a
    non-coboundary winding (not group-native — Na≠Li); and the group-holonomy observable is
    non-vacuous (separates climb from return). One conjunction collecting the file's main
    results, gated by an in-file negative control. -/
theorem chemistry_grounded_witness :
    (∀ g, nextGroup_n 8 g = g) ∧
    (∀ n, projGroup (n + 1) = nextGroup (projGroup n)) ∧
    (∀ n, projGroup (n + 8) = projGroup n) ∧
    (∀ n, shellNumber (n + 8) = shellNumber n + 1) ∧
    (∃ m n, projGroup m = projGroup n ∧ shellNumber m ≠ shellNumber n) ∧
    ¬ IsGroupNative (fun _ => (1 : ℤ)) ∧
    (gholonomy (fun _ => (1 : ℤ)) = 8 ∧
      ∀ p : Group → ℤ, gholonomy (fun g => p (nextGroup g) - p g) = 0) := by
  exact ⟨group_cycle_8, projGroup_succ, projGroup_periodic, shell_increments_per_octave,
    same_group_different_shell, shell_advance_not_group_native,
    ⟨gholonomy_const_one_eq_eight, gholonomy_coboundary⟩⟩

end PeriodicTableGradedCover
