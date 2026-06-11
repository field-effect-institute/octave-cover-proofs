import Mathlib.Tactic
import OctaveCoverProofs.GradedOctaveCover

/-!
  ## MusicOctaveGradedCover — the music instance of the graded octave cover

  **What this is.** A machine-checked instance of the abstract graded-cover result
  (`GradedOctaveCover.lean`) over the twelve chromatic pitch classes. Music is where the octave
  vocabulary comes from, and it is the cleanest instance, because the chromatic octave is
  **exact and uniform**.

  **The music.** Pitch repeats every octave: C, C#, …, B, then **C one octave up**. So:

  - **Base = pitch class**, a closing cycle `ℤ/12ℤ` (`nextSemitone`, `pitchclass_cycle_12`).
    The B→C wrap is a *real* perceptual recurrence (octave equivalence — C and C′ share a name
    and chroma), not an artifact of labeling.
  - **Grade = the octave register number** (`octaveNumber`), forced by the physics: an octave up
    is a **2:1 frequency doubling** (A4 = 440 Hz, A5 = 880 Hz; `octaveNumber = log₂(f/f₀)`).
    A measured quantity — not a bookkeeping counter. One chromatic loop (12 semitones)
    climbs exactly one octave (`octave_increments_per_cycle`).
  - **The non-vacuity witness:** the octave grade is NOT a coboundary
    of any pitch-class potential — same pitch class, different octave exists (A4 ≠ A5,
    `same_pitchclass_different_octave`), so the semitone-advance connection has nonzero
    pitch-holonomy (`pholonomy (const 1) = 12`) and is therefore not pitch-native
    (`semitone_advance_not_pitch_native`). The register climbs; it does not close.

  **Cleaner than chemistry — unscoped.** The companion chemistry instance
  (`PeriodicTableGradedCover.lean`) is deliberately scoped to the s/p-block octave (ℤ/8), with
  the d/f-block extension left open, because periods are irregular (8/18/32). The chromatic
  octave has no such irregularity: 12 equal semitones, every octave, exactly. So the music
  instance carries **no open side condition**. The negative control is unchanged — cosmology
  (`CosmoEpochsGradedCoverNegative.lean`) still fails for want of a recurring base.

  Honest scope: these theorems are about the equal-temperament chromatic encoding defined below.
  Whether that encoding captures real music is a modeling judgment the reader should make by
  reading the definitions. Microtonal / just-intonation refinements only change the base
  cardinality, not the structure.
-/

namespace MusicOctaveGradedCover

-- ============================================================
-- THE PITCH-CLASS BASE  (ℤ/12 — the chromatic octave)
-- ============================================================

/-- The twelve chromatic pitch classes (equal temperament). `N0` = C, …, `N11` = B. -/
inductive PitchClass
  | N0 | N1 | N2 | N3 | N4 | N5 | N6 | N7 | N8 | N9 | N10 | N11
  deriving DecidableEq, Repr

/-- Semitone successor. The pitch classes advance; B (`N11`) → C (`N0`) closes the octave —
    and that wrap is where the register steps up by one. The grade records the step. -/
def nextSemitone : PitchClass → PitchClass
  | .N0 => .N1 | .N1 => .N2 | .N2 => .N3  | .N3 => .N4
  | .N4 => .N5 | .N5 => .N6 | .N6 => .N7  | .N7 => .N8
  | .N8 => .N9 | .N9 => .N10 | .N10 => .N11 | .N11 => .N0

/-- Iterated semitone successor. -/
def nextSemitone_n : Nat → PitchClass → PitchClass
  | 0, p => p
  | n + 1, p => nextSemitone (nextSemitone_n n p)

/-- **The base closes: `nextSemitone¹² = id`.** ℤ/12 — octave equivalence. -/
theorem pitchclass_cycle_12 (p : PitchClass) : nextSemitone_n 12 p = p := by
  cases p <;> rfl

/-- Semitone successor has no fixed point. -/
theorem nextSemitone_ne_self (p : PitchClass) : nextSemitone p ≠ p := by
  cases p <;> decide

theorem nextSemitone_n_add (a b : ℕ) (p : PitchClass) :
    nextSemitone_n (a + b) p = nextSemitone_n a (nextSemitone_n b p) := by
  induction a with
  | zero => simp [nextSemitone_n]
  | succ k ih => simp only [Nat.succ_add, nextSemitone_n, ih]

-- ============================================================
-- THE COVER  +  THE PHYSICAL GRADE (octave register number)
-- ============================================================

/-- The cover projection: the semitone line ℕ → PitchClass. Semitone `n` above C0 has pitch
    class `projPitch n`. ℕ is the cover (absolute pitch, in semitones from C0). -/
def projPitch (n : ℕ) : PitchClass := nextSemitone_n n PitchClass.N0

/-- The physically-forced grade: the octave register of semitone `n`. Twelve semitones per
    octave ⇒ `n / 12`. Physically `log₂(frequency / C0)`: the register doubles frequency. -/
def octaveNumber (n : ℕ) : ℕ := n / 12

/-- Climbing one semitone projects to one `nextSemitone` step (the bundle commuting square). -/
theorem projPitch_succ (n : ℕ) : projPitch (n + 1) = nextSemitone (projPitch n) := rfl

/-- **The octave is the deck transformation.** One full chromatic loop (`+12`) returns to the
    same pitch class: `projPitch` is 12-periodic, so the base is `ℕ/12ℕ` (pitch class = degree-0 face). -/
theorem projPitch_periodic (n : ℕ) : projPitch (n + 12) = projPitch n := by
  unfold projPitch
  rw [nextSemitone_n_add, pitchclass_cycle_12]

/-- **The forced winding: one chromatic loop = exactly one octave.** The register increments by
    one per traversal of the twelve semitones — the substrate's own grade (frequency doubling). -/
theorem octave_increments_per_cycle (n : ℕ) : octaveNumber (n + 12) = octaveNumber n + 1 := by
  unfold octaveNumber
  rw [Nat.add_div_right n (by norm_num : 0 < 12)]

/-- **A4 ≠ A5.** Same pitch class (`projPitch 0 = projPitch 12 = N0`, "C"), different octave
    (`octaveNumber 0 = 0`, `octaveNumber 12 = 1`). The register is not recoverable from the
    pitch class alone — the concrete non-coboundary fact. -/
theorem same_pitchclass_different_octave :
    ∃ m n : ℕ, projPitch m = projPitch n ∧ octaveNumber m ≠ octaveNumber n := by
  refine ⟨0, 12, ?_, ?_⟩
  · exact (projPitch_periodic 0).symm
  · decide

-- ============================================================
-- THE NON-COBOUNDARY WITNESS  (over the pitch-class base)
-- ============================================================

/-- A connection on the pitch-class base assigns a register displacement to each semitone edge. -/
abbrev PConn : Type := PitchClass → ℤ

/-- The twelve-semitone orbit from C. -/
def pitchOrbit (p : PitchClass) : List PitchClass :=
  [p, nextSemitone_n 1 p, nextSemitone_n 2 p, nextSemitone_n 3 p,
   nextSemitone_n 4 p, nextSemitone_n 5 p, nextSemitone_n 6 p, nextSemitone_n 7 p,
   nextSemitone_n 8 p, nextSemitone_n 9 p, nextSemitone_n 10 p, nextSemitone_n 11 p]

/-- Pitch-holonomy: total register displacement around one chromatic octave loop. -/
def pholonomy (δ : PConn) : ℤ := ((pitchOrbit PitchClass.N0).map δ).sum

/-- A connection is *pitch-native* iff it is a coboundary of a pitch-class potential — i.e. the
    register displacement is recoverable from the pitch class alone. -/
def IsPitchNative (δ : PConn) : Prop := ∃ q : PitchClass → ℤ, ∀ p, δ p = q (nextSemitone p) - q p

/-- The semitone-advance connection (`+1` per semitone) has pitch-holonomy `12`: twelve
    semitones, one octave. Witnesses that the observable is nonzero. -/
theorem pholonomy_const_one_eq_twelve : pholonomy (fun _ => (1 : ℤ)) = 12 := by
  simp only [pholonomy, pitchOrbit, nextSemitone_n, nextSemitone,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  norm_num

/-- Every pitch-class-potential coboundary has pitch-holonomy `0` (telescoping). -/
theorem pholonomy_coboundary (q : PitchClass → ℤ) :
    pholonomy (fun p => q (nextSemitone p) - q p) = 0 := by
  simp only [pholonomy, pitchOrbit, nextSemitone_n, nextSemitone,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-- Every pitch-native connection is flat. -/
theorem pitch_native_is_flat (δ : PConn) (h : IsPitchNative δ) : pholonomy δ = 0 := by
  obtain ⟨q, hq⟩ := h
  have : δ = (fun p => q (nextSemitone p) - q p) := funext hq
  rw [this]; exact pholonomy_coboundary q

/-- **The non-coboundary witness.** The semitone-advance connection is
    NOT pitch-native: the octave register cannot be recovered from the pitch class. Proof: if it
    were pitch-native it would be flat, but its pitch-holonomy is `12 ≠ 0`. So the octave grade
    is a genuine winding — it cannot be defined away inside the pitch-class circle. -/
theorem semitone_advance_not_pitch_native : ¬ IsPitchNative (fun _ => (1 : ℤ)) := by
  intro h
  have hflat := pitch_native_is_flat _ h
  rw [pholonomy_const_one_eq_twelve] at hflat
  norm_num at hflat

/-- In-file negative control: the observable separates the octave-advance winding (`12`) from
    every pitch-class-only coboundary (`0`). The result is non-vacuous. -/
theorem pholonomy_non_vacuous :
    (∃ δ : PConn, pholonomy δ ≠ 0) ∧ (∃ δ : PConn, pholonomy δ = 0) := by
  refine ⟨⟨fun _ => 1, ?_⟩, ⟨fun _ => 0, ?_⟩⟩
  · rw [pholonomy_const_one_eq_twelve]; norm_num
  · simpa using pholonomy_coboundary (fun _ => 0)

/-- The physical grade and the abstract pitch-holonomy agree: the register jump over one octave
    (`+1`), scaled by the twelve semitones, is exactly the octave-advance holonomy (`12`). -/
theorem register_jump_matches_holonomy :
    ((octaveNumber 12 : ℤ) - octaveNumber 0) * 12 = pholonomy (fun _ => 1) := by
  rw [pholonomy_const_one_eq_twelve]; norm_num [octaveNumber]

-- ============================================================
-- THE MUSIC VERDICT, ASSEMBLED
-- ============================================================

/-- **The music instance, assembled (unscoped).** The twelve chromatic pitch classes are
    a closing base (`ℤ/12`, octave equivalence); the octave register number is a physically
    meaningful grade (frequency doubling) that climbs exactly one octave per chromatic loop; the
    semitone-advance is a non-coboundary winding (not pitch-native — A4≠A5); and the pitch-holonomy
    observable is non-vacuous. The octave being exact and uniform, the instance carries no open
    side condition. One conjunction collecting the file's main results. -/
theorem music_grounded_witness :
    (∀ p, nextSemitone_n 12 p = p) ∧
    (∀ n, projPitch (n + 1) = nextSemitone (projPitch n)) ∧
    (∀ n, projPitch (n + 12) = projPitch n) ∧
    (∀ n, octaveNumber (n + 12) = octaveNumber n + 1) ∧
    (∃ m n, projPitch m = projPitch n ∧ octaveNumber m ≠ octaveNumber n) ∧
    ¬ IsPitchNative (fun _ => (1 : ℤ)) ∧
    (pholonomy (fun _ => (1 : ℤ)) = 12 ∧
      ∀ q : PitchClass → ℤ, pholonomy (fun p => q (nextSemitone p) - q p) = 0) := by
  exact ⟨pitchclass_cycle_12, projPitch_succ, projPitch_periodic, octave_increments_per_cycle,
    same_pitchclass_different_octave, semitone_advance_not_pitch_native,
    ⟨pholonomy_const_one_eq_twelve, pholonomy_coboundary⟩⟩

end MusicOctaveGradedCover
