import Mathlib
import IndisputableMonolith.Verification.GWTC3PosteriorManifest

/-!
# GWTC-3 Ringdown ZIP Schema

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

This module records the ZIP central-directory schema of
`IGWN-GWTC3-TGR-v1-rin.zip`, fetched by HTTP range request (central
directory only, no 1.44 GB payload download).

Companion script:

* `papers/reproducibility/gwtc3_ringdown_zip_schema.py`

Live metadata result:

* source ZIP size: `1,444,203,951` bytes
* central-directory offset: `1,444,176,371`
* central-directory size: `27,558` bytes
* entry count: `244`
* extension counts: `.h5 = 243`, `<none> = 1`
* top-level prefix: `rin = 244`
* total compressed size from entries: `1,444,151,741` bytes
* total uncompressed size from entries: `1,963,931,876` bytes

This is schema inspection only, not posterior likelihood.
Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Verification
namespace GWTC3RingdownZipSchema

open IndisputableMonolith.Verification.GWTC3PosteriorManifest

/-! ## §1. Schema constants -/

def ringdownZipSourceSizeBytes : Nat := 1444203951
def ringdownZipCentralDirectoryOffset : Nat := 1444176371
def ringdownZipCentralDirectorySize : Nat := 27558
def ringdownZipEntryCount : Nat := 244
def ringdownZipH5Count : Nat := 243
def ringdownZipDirectoryMarkerCount : Nat := 1
def ringdownZipTopLevelRinCount : Nat := 244
def ringdownZipTotalCompressedSize : Nat := 1444151741
def ringdownZipTotalUncompressedSize : Nat := 1963931876

/-! ## §2. Positivity and count facts -/

theorem ringdown_zip_source_size_pos : 0 < ringdownZipSourceSizeBytes := by
  unfold ringdownZipSourceSizeBytes
  decide

theorem ringdown_zip_cd_size_pos : 0 < ringdownZipCentralDirectorySize := by
  unfold ringdownZipCentralDirectorySize
  decide

theorem ringdown_zip_entry_count_pos : 0 < ringdownZipEntryCount := by
  unfold ringdownZipEntryCount
  decide

theorem ringdown_zip_extension_count_sum :
    ringdownZipH5Count + ringdownZipDirectoryMarkerCount = ringdownZipEntryCount := by
  unfold ringdownZipH5Count ringdownZipDirectoryMarkerCount ringdownZipEntryCount
  decide

theorem ringdown_zip_top_level_count_eq_entries :
    ringdownZipTopLevelRinCount = ringdownZipEntryCount := by
  unfold ringdownZipTopLevelRinCount ringdownZipEntryCount
  rfl

theorem ringdown_zip_total_uncompressed_gt_compressed :
    ringdownZipTotalCompressedSize < ringdownZipTotalUncompressedSize := by
  unfold ringdownZipTotalCompressedSize ringdownZipTotalUncompressedSize
  decide

theorem ringdown_zip_cd_inside_source :
    ringdownZipCentralDirectoryOffset + ringdownZipCentralDirectorySize <
      ringdownZipSourceSizeBytes := by
  unfold ringdownZipCentralDirectoryOffset ringdownZipCentralDirectorySize
    ringdownZipSourceSizeBytes
  decide

/-! ## §3. Master cert -/

structure GWTC3RingdownZipSchemaCert where
  source_size_pos : 0 < ringdownZipSourceSizeBytes
  central_directory_size_pos : 0 < ringdownZipCentralDirectorySize
  entry_count_pos : 0 < ringdownZipEntryCount
  extension_count_sum :
    ringdownZipH5Count + ringdownZipDirectoryMarkerCount = ringdownZipEntryCount
  top_level_count_eq_entries :
    ringdownZipTopLevelRinCount = ringdownZipEntryCount
  total_uncompressed_gt_compressed :
    ringdownZipTotalCompressedSize < ringdownZipTotalUncompressedSize
  central_directory_inside_source :
    ringdownZipCentralDirectoryOffset + ringdownZipCentralDirectorySize <
      ringdownZipSourceSizeBytes
  ringdown_manifest_key :
    ringdownFile.key = "IGWN-GWTC3-TGR-v1-rin.zip"

def gwtc3RingdownZipSchemaCert : GWTC3RingdownZipSchemaCert where
  source_size_pos := ringdown_zip_source_size_pos
  central_directory_size_pos := ringdown_zip_cd_size_pos
  entry_count_pos := ringdown_zip_entry_count_pos
  extension_count_sum := ringdown_zip_extension_count_sum
  top_level_count_eq_entries := ringdown_zip_top_level_count_eq_entries
  total_uncompressed_gt_compressed := ringdown_zip_total_uncompressed_gt_compressed
  central_directory_inside_source := ringdown_zip_cd_inside_source
  ringdown_manifest_key := ringdown_file_key

theorem gwtc3RingdownZipSchemaCert_inhabited :
    Nonempty GWTC3RingdownZipSchemaCert :=
  ⟨gwtc3RingdownZipSchemaCert⟩

/-- One-statement schema theorem for the ringdown ZIP. -/
theorem gwtc3_ringdown_zip_schema_one_statement :
    (ringdownZipEntryCount = 244) ∧
    (ringdownZipH5Count = 243) ∧
    (ringdownZipDirectoryMarkerCount = 1) ∧
    (ringdownZipH5Count + ringdownZipDirectoryMarkerCount = ringdownZipEntryCount) ∧
    (ringdownZipTopLevelRinCount = ringdownZipEntryCount) ∧
    (ringdownZipTotalCompressedSize < ringdownZipTotalUncompressedSize) ∧
    (ringdownFile.key = "IGWN-GWTC3-TGR-v1-rin.zip") ∧
    Nonempty GWTC3RingdownZipSchemaCert :=
  ⟨rfl, rfl, rfl,
   ringdown_zip_extension_count_sum,
   ringdown_zip_top_level_count_eq_entries,
   ringdown_zip_total_uncompressed_gt_compressed,
   ringdown_file_key,
   gwtc3RingdownZipSchemaCert_inhabited⟩

end GWTC3RingdownZipSchema
end Verification
end IndisputableMonolith
