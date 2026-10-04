import Verification.NumericCertificateDigestBridge

open NumericCertificateDigestBridge NumericSQLIntervalBounds
open NumericRoundingCertificates NumericRealRounding

set_option maxRecDepth 8192

-- These are deliberately small test adapters, not SHA-256 or JSON implementations.
def lengthDigest (bytes : List UInt8) : Digest32 := fun _ => UInt8.ofNat bytes.length
def halfPayload : ParsedCertificate binary64 := ⟨1 / 2, 1 / 2, halfEncoding⟩
def zeroPayload : ParsedCertificate binary64 := ⟨0, 0, positiveZero⟩
def wrongPayload : ParsedCertificate binary64 := ⟨1 / 2, 1 / 2, positiveZero⟩
def reversedPayload : ParsedCertificate binary64 := ⟨1, 1 / 2, halfEncoding⟩
def pointInterval (x : ℚ) : RatInterval := ⟨x, x, le_refl _⟩
def sqrtTwoBounds : RatInterval :=
  ⟨1709679290002018430137083 / 1208925819614629174706176,
   1709679290002018430137084 / 1208925819614629174706176, by decide +kernel⟩
def sqrtTwoEncoding : FloatRepresentation binary64 :=
  ⟨false, ⟨4609047870845172685, by decide +kernel⟩⟩
def sqrtTwoPayload : ParsedCertificate binary64 :=
  ⟨sqrtTwoBounds.lo, sqrtTwoBounds.hi, sqrtTwoEncoding⟩

def toyParser (bytes : List UInt8) : Option (ParsedCertificate binary64) :=
  if bytes = [0] then some halfPayload
  else if bytes = [1] then some wrongPayload
  else if bytes = [2] then some reversedPayload
  else if bytes = [3] then some sqrtTwoPayload
  else none

def alternateParser (bytes : List UInt8) : Option (ParsedCertificate binary64) :=
  if bytes = [0] then some zeroPayload else none

example : validatePayload lengthDigest toyParser (lengthDigest [0]) [0] = some halfPayload := by
  decide +kernel
example : validatePayload lengthDigest toyParser (fun _ => 0) [0] = none := by decide +kernel
example : validatePayload lengthDigest toyParser (lengthDigest []) [] = none := by decide +kernel
example : validatePayload lengthDigest toyParser (lengthDigest [0]) [1] = none := by decide +kernel
example : validatePayload lengthDigest toyParser (lengthDigest [2]) [2] = none := by decide +kernel
example : validatePayload lengthDigest toyParser (lengthDigest [4]) [4] = none := by decide +kernel

-- Constant/length digests admit collisions; matching outputs cannot recover the bytes.
example : lengthDigest [0] = lengthDigest [1] ∧ ([0] : List UInt8) ≠ [1] := by decide +kernel
example : ∃ (d : DigestFunction) (a b : List UInt8), d a = d b ∧ a ≠ b :=
  digest_equality_does_not_imply_bytes_equality

-- Identical bytes and digest but different decoders can give different accepted meanings.
example : validatePayload lengthDigest alternateParser (lengthDigest [0]) [0] =
    some zeroPayload := by decide +kernel
example : halfPayload.claimedFloat ≠ zeroPayload.claimedFloat := by decide +kernel

-- A parsed record really comes from the selected parser and those same input bytes.
example : parsePayload toyParser [0] = some halfPayload := by
  exact ((validate_payload_eq_some_iff lengthDigest toyParser (lengthDigest [0]) [0]
    halfPayload).mp (by decide +kernel)).2.1
example : (checkedPayloadOfAccepted lengthDigest toyParser (lengthDigest [0]) [0]
    halfPayload (by decide +kernel)).rawBytes = [0] := rfl

example : roundNearestEven binary64 (1 / 2) = halfPayload.claimedFloat := by
  exact rational_certificate_validation lengthDigest toyParser (lengthDigest [0]) [0]
    halfPayload (1 / 2) (by decide +kernel) (le_refl _) (le_refl _)

-- Composition certifies an irrational target, using a root witness with the parsed endpoints.
example : realRound binary64 (sqlTarget 2 1 1) = sqrtTwoPayload.claimedFloat := by
  apply sql_e2e_verified_pipeline lengthDigest toyParser (lengthDigest [3]) [3] sqrtTwoPayload
    (by decide +kernel) (pointInterval 2) (pointInterval 1) (pointInterval 1) sqrtTwoBounds
    (by decide) (by decide) (by decide) 2 1 1
    (by norm_num [containsReal, pointInterval]) (by norm_num [containsReal, pointInterval])
    (by norm_num [containsReal, pointInterval])
  · decide +kernel
  · rfl
  · rfl

-- A valid digest/parse/rounding record does not itself enclose an unrelated SQL target.
example : checkSqrtWitness (pointInterval 2) (pointInterval (1 / 2)) = false := by
  decide +kernel
example : sqrtTwoBounds.lo ≠ halfPayload.lo := by decide +kernel
