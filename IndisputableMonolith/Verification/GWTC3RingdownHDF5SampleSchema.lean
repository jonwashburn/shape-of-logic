import Mathlib
import IndisputableMonolith.Verification.GWTC3RingdownZipSchema

/-!
# GWTC-3 Ringdown HDF5 Sample Schema

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

This module records the first schema-level inspection of an actual HDF5
posterior member from the GWTC-3 ringdown ZIP, without downloading the
full 1.44 GB archive.

Companion script:

* `papers/reproducibility/gwtc3_ringdown_hdf5_sample_schema.py`

Method:

* Read ZIP central directory by HTTP range request.
* Select the smallest `.h5` member:
  `rin/rin_S190727h_pyring_DS_1mode_10M.h5`.
* Range-read that member's local header and compressed bytes only.
* Inflate locally and inspect the HDF5 schema with `h5py`.

Live metadata result:

* compressed size: `679,110` bytes
* uncompressed size: `931,208` bytes
* local-header offset: `66,237,197`
* data offset: `66,237,294`
* HDF5 object count: `97`
* group count: `14`
* dataset count: `83`
* root attr count: `0`
* key posterior dataset: `/EXP6/posterior_samples`
* posterior sample count: `15,114`
* posterior field count: `7`

This is one-member schema inspection only, not posterior likelihood.
Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Verification
namespace GWTC3RingdownHDF5SampleSchema

open IndisputableMonolith.Verification.GWTC3RingdownZipSchema

/-! ## §1. Sample member constants -/

def sampleMemberName : String := "rin/rin_S190727h_pyring_DS_1mode_10M.h5"
def sampleCompressedSize : Nat := 679110
def sampleUncompressedSize : Nat := 931208
def sampleLocalHeaderOffset : Nat := 66237197
def sampleDataOffset : Nat := 66237294
def sampleHDF5ObjectCount : Nat := 97
def sampleGroupCount : Nat := 14
def sampleDatasetCount : Nat := 83
def sampleRootAttrCount : Nat := 0
def posteriorSamplesDatasetPath : String := "/EXP6/posterior_samples"
def posteriorSamplesCount : Nat := 15114
def posteriorFieldCount : Nat := 7

/-! ## §2. Schema facts -/

theorem sample_sizes_pos :
    0 < sampleCompressedSize ∧ 0 < sampleUncompressedSize := by
  unfold sampleCompressedSize sampleUncompressedSize
  decide

theorem sample_uncompressed_gt_compressed :
    sampleCompressedSize < sampleUncompressedSize := by
  unfold sampleCompressedSize sampleUncompressedSize
  decide

theorem sample_object_count_split :
    sampleGroupCount + sampleDatasetCount = sampleHDF5ObjectCount := by
  unfold sampleGroupCount sampleDatasetCount sampleHDF5ObjectCount
  decide

theorem sample_posterior_samples_nonempty :
    0 < posteriorSamplesCount := by
  unfold posteriorSamplesCount
  decide

theorem sample_posterior_field_count_pos :
    0 < posteriorFieldCount := by
  unfold posteriorFieldCount
  decide

theorem sample_member_is_h5 :
    sampleMemberName = "rin/rin_S190727h_pyring_DS_1mode_10M.h5" := rfl

theorem sample_posterior_dataset_named :
    posteriorSamplesDatasetPath = "/EXP6/posterior_samples" := rfl

/-! ## §3. Master cert -/

structure GWTC3RingdownHDF5SampleSchemaCert where
  sample_member_named :
    sampleMemberName = "rin/rin_S190727h_pyring_DS_1mode_10M.h5"
  sizes_positive :
    0 < sampleCompressedSize ∧ 0 < sampleUncompressedSize
  uncompressed_gt_compressed :
    sampleCompressedSize < sampleUncompressedSize
  object_count_split :
    sampleGroupCount + sampleDatasetCount = sampleHDF5ObjectCount
  posterior_dataset_named :
    posteriorSamplesDatasetPath = "/EXP6/posterior_samples"
  posterior_samples_nonempty :
    0 < posteriorSamplesCount
  posterior_field_count_pos :
    0 < posteriorFieldCount
  ringdown_zip_schema_available :
    Nonempty GWTC3RingdownZipSchemaCert

def gwtc3RingdownHDF5SampleSchemaCert :
    GWTC3RingdownHDF5SampleSchemaCert where
  sample_member_named := sample_member_is_h5
  sizes_positive := sample_sizes_pos
  uncompressed_gt_compressed := sample_uncompressed_gt_compressed
  object_count_split := sample_object_count_split
  posterior_dataset_named := sample_posterior_dataset_named
  posterior_samples_nonempty := sample_posterior_samples_nonempty
  posterior_field_count_pos := sample_posterior_field_count_pos
  ringdown_zip_schema_available := gwtc3RingdownZipSchemaCert_inhabited

theorem gwtc3RingdownHDF5SampleSchemaCert_inhabited :
    Nonempty GWTC3RingdownHDF5SampleSchemaCert :=
  ⟨gwtc3RingdownHDF5SampleSchemaCert⟩

/-- One-statement HDF5 sample schema theorem. -/
theorem gwtc3_ringdown_hdf5_sample_schema_one_statement :
    (sampleMemberName = "rin/rin_S190727h_pyring_DS_1mode_10M.h5") ∧
    (sampleGroupCount + sampleDatasetCount = sampleHDF5ObjectCount) ∧
    (posteriorSamplesDatasetPath = "/EXP6/posterior_samples") ∧
    (0 < posteriorSamplesCount) ∧
    (posteriorFieldCount = 7) ∧
    Nonempty GWTC3RingdownHDF5SampleSchemaCert :=
  ⟨sample_member_is_h5,
   sample_object_count_split,
   sample_posterior_dataset_named,
   sample_posterior_samples_nonempty,
   rfl,
   gwtc3RingdownHDF5SampleSchemaCert_inhabited⟩

end GWTC3RingdownHDF5SampleSchema
end Verification
end IndisputableMonolith
