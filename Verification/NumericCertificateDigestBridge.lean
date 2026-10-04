/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.NumericSQLIntervalBounds
import Mathlib.Data.Fintype.Pi

/-!
# Conditional byte-certificate composition

The digest algorithm and decoder are explicit pure-function parameters. Neither
SHA-256 nor JSON is implemented here. The expected digest, decoder and magnitude
grid are caller-supplied context; a digest match authenticates none of them.
The accepted parsed record is linked to the actual input bytes. Numerical
soundness additionally requires real enclosure, supplied explicitly or derived
for sqrt(hbar/(mass*frequency)) from a checked root witness and localized inputs.
-/

namespace NumericCertificateDigestBridge

open NumericRoundingCertificates NumericSQLIntervalBounds NumericRealRounding

abbrev Digest32 := Fin 32 → UInt8
abbrev DigestFunction := List UInt8 → Digest32

/-- A checked wrapper, relative to the specified digest function, not an authenticated object. -/
structure RawCertificatePayload (digest : DigestFunction) where
  rawBytes : List UInt8
  expectedDigest : Digest32
  digestValid : digest rawBytes = expectedDigest

/-- The magnitude grid is fixed by the decoding context, not inferred from a trusted byte tag. -/
structure ParsedCertificate (g : MagnitudeGrid) where
  lo : ℚ
  hi : ℚ
  claimedFloat : FloatRepresentation g
  deriving DecidableEq

abbrev PayloadParser (g : MagnitudeGrid) := List UInt8 → Option (ParsedCertificate g)

/-- Explicit decoder parameter; this adapter is not a JSON grammar implementation. -/
def parsePayload {g : MagnitudeGrid} (parser : PayloadParser g) (bytes : List UInt8) :
    Option (ParsedCertificate g) := parser bytes

/-- Functional congruence holds for every digest, including insecure ones. -/
theorem digest_preserved_of_bytes_eq (digest : DigestFunction) (a b : List UInt8)
    (h : a = b) : digest a = digest b := congrArg digest h

/-- Different digest outputs imply different inputs; the converse is not asserted. -/
theorem digest_integrity_soundness (digest : DigestFunction) (a b : List UInt8)
    (h : digest a ≠ digest b) : a ≠ b := fun hab => h (congrArg digest hab)

/-- Check against an external expected digest, then decode those same bytes and check the record. -/
def validatePayload {g : MagnitudeGrid} (digest : DigestFunction) (parser : PayloadParser g)
    (expected : Digest32) (bytes : List UInt8) : Option (ParsedCertificate g) :=
  if digest bytes = expected then
    match parsePayload parser bytes with
    | none => none
    | some p =>
      if checkIntervalCertificate g p.lo p.hi p.claimedFloat = .decided p.claimedFloat then
        some p
      else none
  else none

/-- Acceptance exposes all three gates and their common parsed record. -/
theorem validate_payload_eq_some_iff {g : MagnitudeGrid}
    (digest : DigestFunction) (parser : PayloadParser g)
    (expected : Digest32) (bytes : List UInt8) (p : ParsedCertificate g) :
    validatePayload digest parser expected bytes = some p ↔
      digest bytes = expected ∧ parsePayload parser bytes = some p ∧
      checkIntervalCertificate g p.lo p.hi p.claimedFloat = .decided p.claimedFloat := by
  by_cases hd : digest bytes = expected
  · cases hp : parsePayload parser bytes with
    | none => simp [validatePayload, hd, hp]
    | some q =>
      simp only [validatePayload, if_pos hd, hp]
      by_cases hc : checkIntervalCertificate g q.lo q.hi q.claimedFloat = .decided q.claimedFloat
      · rw [if_pos hc]
        simp only [Option.some.injEq]
        constructor
        · intro hqp
          subst q
          exact ⟨hd, rfl, hc⟩
        · rintro ⟨_, hqp, _⟩
          exact hqp
      · rw [if_neg hc]
        constructor
        · intro h
          cases h
        · rintro ⟨_, hqp, hcheck⟩
          cases Option.some.inj hqp
          exact (hc hcheck).elim
  · simp [validatePayload, hd]

/-- Accepted payloads can be wrapped with their actual checked digest equation. -/
def checkedPayloadOfAccepted {g : MagnitudeGrid}
    (digest : DigestFunction) (parser : PayloadParser g)
    (expected : Digest32) (bytes : List UInt8) (p : ParsedCertificate g)
    (h : validatePayload digest parser expected bytes = some p) : RawCertificatePayload digest :=
  ⟨bytes, expected, (validate_payload_eq_some_iff digest parser expected bytes p).mp h |>.1⟩

theorem accepted_bounds_ordered {g : MagnitudeGrid}
    (digest : DigestFunction) (parser : PayloadParser g)
    (expected : Digest32) (bytes : List UInt8) (p : ParsedCertificate g)
    (h : validatePayload digest parser expected bytes = some p) : p.lo ≤ p.hi := by
  have hc := ((validate_payload_eq_some_iff digest parser expected bytes p).mp h).2.2
  exact ((interval_certificate_decided_iff g p.lo p.hi p.claimedFloat).mp hc).1

theorem reject_wrong_digest {g : MagnitudeGrid}
    (digest : DigestFunction) (parser : PayloadParser g)
    (expected : Digest32) (bytes : List UInt8) (h : digest bytes ≠ expected) :
    validatePayload digest parser expected bytes = none := by
  simp [validatePayload, h]

theorem reject_failed_parse {g : MagnitudeGrid}
    (digest : DigestFunction) (parser : PayloadParser g)
    (expected : Digest32) (bytes : List UInt8) (h : parsePayload parser bytes = none) :
    validatePayload digest parser expected bytes = none := by
  simp [validatePayload, h]

/-- Enclosure is a separate mathematical premise; a digest match cannot supply it. -/
theorem end_to_end_certificate_validation {g : MagnitudeGrid}
    (digest : DigestFunction) (parser : PayloadParser g)
    (expected : Digest32) (bytes : List UInt8) (p : ParsedCertificate g) (x : ℝ)
    (haccept : validatePayload digest parser expected bytes = some p)
    (hlo : (p.lo : ℝ) ≤ x) (hhi : x ≤ (p.hi : ℝ)) :
    realRound g x = p.claimedFloat := by
  have hc := ((validate_payload_eq_some_iff digest parser expected bytes p).mp haccept).2.2
  exact interval_certificate_real_sound g p.lo p.hi x p.claimedFloat hc hlo hhi

/-- Rational specialization agrees with the earlier executable rounding specification. -/
theorem rational_certificate_validation {g : MagnitudeGrid}
    (digest : DigestFunction) (parser : PayloadParser g)
    (expected : Digest32) (bytes : List UInt8) (p : ParsedCertificate g) (x : ℚ)
    (haccept : validatePayload digest parser expected bytes = some p)
    (hlo : p.lo ≤ x) (hhi : x ≤ p.hi) : roundNearestEven g x = p.claimedFloat := by
  have hr := end_to_end_certificate_validation digest parser expected bytes p (x : ℝ) haccept
    (by exact_mod_cast hlo) (by exact_mod_cast hhi)
  simpa only [realRound_ratCast] using hr

/-- SQL inputs are external; the checked root witness has exactly the parsed endpoints. -/
theorem sql_e2e_verified_pipeline {g : MagnitudeGrid}
    (digest : DigestFunction) (parser : PayloadParser g)
    (expected : Digest32) (bytes : List UInt8) (p : ParsedCertificate g)
    (haccept : validatePayload digest parser expected bytes = some p)
    (H M W R : RatInterval) (hh : 0 < H.lo) (hm : 0 < M.lo) (hw : 0 < W.lo)
    (hbar m omega : ℝ) (hH : containsReal H hbar)
    (hM : containsReal M m) (hW : containsReal W omega)
    (hroot : checkSqrtWitness (radicandInterval H M W hh hm hw) R = true)
    (hlo : R.lo = p.lo) (hhi : R.hi = p.hi) :
    realRound g (sqlTarget hbar m omega) = p.claimedFloat := by
  have he := sql_interval_enclosure H M W R hh hm hw hbar m omega hH hM hW hroot
  rw [containsReal, hlo, hhi] at he
  exact end_to_end_certificate_validation digest parser expected bytes p _ haccept he.1 he.2

/-- The abstraction admits collisions; equal digest outputs alone cannot establish byte equality. -/
theorem digest_equality_does_not_imply_bytes_equality :
    ∃ (digest : DigestFunction) (a b : List UInt8), digest a = digest b ∧ a ≠ b := by
  exact ⟨fun _ _ => 0, [], [0], rfl, by decide⟩

structure NumericCertificateDigestBridgeSuite : Prop where
  digest_congruence : ∀ digest : DigestFunction, ∀ a b : List UInt8,
    a = b → digest a = digest b
  digest_separation : ∀ digest : DigestFunction, ∀ a b : List UInt8,
    digest a ≠ digest b → a ≠ b
  acceptance : ∀ g : MagnitudeGrid, ∀ digest : DigestFunction, ∀ parser : PayloadParser g,
    ∀ expected : Digest32, ∀ bytes : List UInt8, ∀ p : ParsedCertificate g,
    validatePayload digest parser expected bytes = some p ↔
      digest bytes = expected ∧ parsePayload parser bytes = some p ∧
      checkIntervalCertificate g p.lo p.hi p.claimedFloat = .decided p.claimedFloat
  real_soundness : ∀ g : MagnitudeGrid, ∀ digest : DigestFunction, ∀ parser : PayloadParser g,
    ∀ expected : Digest32, ∀ bytes : List UInt8, ∀ p : ParsedCertificate g, ∀ x : ℝ,
    validatePayload digest parser expected bytes = some p →
    (p.lo : ℝ) ≤ x → x ≤ (p.hi : ℝ) → realRound g x = p.claimedFloat
  sql_soundness : ∀ g : MagnitudeGrid, ∀ digest : DigestFunction, ∀ parser : PayloadParser g,
    ∀ expected : Digest32, ∀ bytes : List UInt8, ∀ p : ParsedCertificate g,
    validatePayload digest parser expected bytes = some p →
    ∀ H M W R : RatInterval, ∀ hh : 0 < H.lo, ∀ hm : 0 < M.lo, ∀ hw : 0 < W.lo,
    ∀ hbar m omega : ℝ, containsReal H hbar → containsReal M m → containsReal W omega →
    checkSqrtWitness (radicandInterval H M W hh hm hw) R = true →
    R.lo = p.lo → R.hi = p.hi → realRound g (sqlTarget hbar m omega) = p.claimedFloat

theorem numeric_digest_bridge_master_suite : NumericCertificateDigestBridgeSuite := {
  digest_congruence := digest_preserved_of_bytes_eq
  digest_separation := digest_integrity_soundness
  acceptance := fun _ => validate_payload_eq_some_iff
  real_soundness := fun _ => end_to_end_certificate_validation
  sql_soundness := fun _ => sql_e2e_verified_pipeline
}

end NumericCertificateDigestBridge
