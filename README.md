# Check It Yourself — A Verification Guide

## What this repository is

The articles you came from make one structural claim: **a repeating scale with a forced register** — the same loop closing while a counter is pushed up one level — shows up identically in music (octaves), in chemistry (electron shells), and fails, on the record, in cosmology. This repository contains the machine-checked proofs behind that claim, and this guide tells you how to check them yourself, in minutes, without trusting us.

The honest version of the pitch is not "we verified this." It is: **the proof assistant's kernel accepted these proofs, and you can make it re-check them on your own machine.** You are not asked to believe a person. You are asked to run a check.

## The four results, in plain language

**1. Music — the octave is forced** (`OctaveCoverProofs/MusicOctaveGradedCover.lean`)
The file encodes the twelve equal-temperament pitch classes as a 12-step loop — the definitions are at the top, and whether they capture real music is yours to judge. Within that encoding, the theorems are unconditional: `pitchclass_cycle_12` proves twelve semitone steps close the loop, `octave_increments_per_cycle` proves the register must go up by exactly one per loop, and `same_pitchclass_different_octave` proves the structure's A4 and A5 are genuinely distinct — same pitch class, different register. The file also proves this isn't bookkeeping you could define away: `semitone_advance_not_pitch_native` shows the climb cannot be expressed inside the pitch-class circle alone.

**2. Chemistry — same shape, different substrate** (`OctaveCoverProofs/PeriodicTableGradedCover.lean`)
The file encodes the periodic table's group structure (scoped, deliberately, to the s- and p-blocks) as the same kind of loop, and proves that within that encoding the shell number is forced up per cycle — the same fourteen-theorem structure as the music file, instantiating the same general theorem.

**3. The general theorem both instantiate** (`OctaveCoverProofs/GradedOctaveCover.lean`, `OctaveCoverProofs/LayerBaseIso.lean`)
The music and chemistry files are not two coincidences. Both are instances of one abstract result: a cyclic base with a graded cover, where closing the base loop forces the grade to increment. The instance files import it; you can read the dependency with your own eyes in the `import` lines.

**4. Cosmology — the system says NO** (`OctaveCoverProofs/CosmoEpochsGradedCoverNegative.lean`)
This is the file to read if you suspect the framework is unfalsifiable. The file encodes the standard cosmic-epoch sequence (Planck era → … → Recombination) as a strict linear order, and proves that this order admits *no* closing successor (`ncg3_no_recurring_base`) — no loop, so no octave, so the pattern **does not apply**, and `ncg5_cosmo_graded_cover_negative` records that failure as a theorem. `ncg6_terminal_order_forced` proves the failure comes from the time-ordering itself, not from how we happened to label the epochs. A framework that can only say yes is a rubber stamp; this is the proof it says no.

## How to check it (10–20 minutes, first run)

You need: git, a terminal, a few GB of disk, and an internet connection.

```bash
# 1. Install elan (the Lean toolchain manager) — one line, official installer:
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh

# 2. Clone and enter:
git clone https://github.com/field-effect-institute/octave-cover-proofs
cd octave-cover-proofs

# 3. Fetch the prebuilt mathematics library cache:
lake exe cache get

# 4. Build — this is the actual check:
lake build
echo $?
```

If the final line prints `0` after `Build completed successfully`, the Lean 4 kernel — a small, independent core that every proof must pass through, the same one used by mathematicians formalizing research mathematics — has re-verified every theorem in this repository on your hardware. Most of the 10–20 minutes is downloading; the verification itself takes seconds.

The toolchain (`lean-toolchain`) and the mathematics library version (`lake-manifest.json`) are pinned, so you build exactly what we built.

## What a passing build establishes — and what it doesn't

**It establishes:** every stated theorem follows, by machine-checked logical deduction, from the stated definitions. No proof contains a gap, an unproven placeholder (`sorry`), or a hidden assumption beyond Lean and its standard mathematics library. The repository uses no `sorry`, no `admit`, no `axiom` declarations, and none of the faster-but-heavier `native_decide` mechanism (which would extend trust to the compiler) — every check goes through the ordinary kernel path.

**It does not establish:**

- **That the definitions are the world.** The proofs certify the *shape*, not the physics. `pitchclass_cycle_12` is a theorem about a 12-element structure we defined; that this structure faithfully models equal-temperament pitch is a modeling judgment you should evaluate yourself — the definitions are short and at the top of each file, and reading them is part of the check.
- **That anyone independent verified this before you.** The receipts in this repository were produced by the authors' own toolchain runs. *Your* build is the independent verification. That is the point of publishing it.
- **The grander claims.** These four files prove (and one disproves) a specific structural pattern in three specific places. They do not prove any broader framework, methodology, or worldview. Anything in the articles beyond these four results is argument, not theorem, and should be weighed as argument.

## How to try to break it

- **Change a definition.** Edit `nextSemitone` so B no longer wraps to C, rebuild — `pitchclass_cycle_12` fails. The proofs are load-bearing on the definitions, not decorative.
- **Hunt for trapdoors.** `grep -rn "sorry\|admit\|axiom" OctaveCoverProofs/` — check that what we just said is true.
- **Audit the axioms.** In any file, after a theorem, add `#print axioms <theorem_name>` and rebuild — Lean prints exactly which axioms the proof rests on.
- **Attack the modeling.** The strongest critique isn't "the proof is wrong" (the kernel settles that); it's "the definition doesn't capture the real thing." Read the definitions and make that case — that's the conversation we're inviting.

## If the build fails — or you break something

A genuine failure on a clean clone with the pinned toolchain would mean the repository does not do what this guide says. Please open an issue with your OS, the command output, and the contents of `lean-toolchain` — that's a real finding, and finding it is what this setup is for.

The same goes for the stronger kind of finding: a case where a definition doesn't capture the real thing it claims to encode. Open an issue, or write to ryan@fieldeffectinstitute.org — accepted refinements go on the record under your name.

## License

Apache-2.0, © Field Effect Institute.
