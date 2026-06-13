import Mathlib
import IndisputableMonolith.Verification.GWTC3RingdownZipSchema

/-!
# GWTC-3 Ringdown Filename Taxonomy

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

This module records the archive-wide filename taxonomy of the 243 HDF5
files in `IGWN-GWTC3-TGR-v1-rin.zip`, using only the ZIP central
directory from Session 118. No posterior samples are read.

Companion script:

* `papers/reproducibility/gwtc3_ringdown_filename_taxonomy.py`

Live taxonomy:

* HDF5 files: `243`
* Events: `26`
* Pipelines: `pyring = 225`, `pseobnrv4hm = 18`
* Categories: `Kerr = 159`, `MMRDNP = 44`, `damped-sinusoid = 22`,
  `waveform = 18`
* Smallest member:
  `rin/rin_S190727h_pyring_DS_1mode_10M.h5`
* Largest member:
  `rin/rin_S191109d_pseobnrv4hm.h5`

This is taxonomy only. No posterior likelihood is computed.
Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Verification
namespace GWTC3RingdownFilenameTaxonomy

open IndisputableMonolith.Verification.GWTC3RingdownZipSchema

/-! ## §1. Taxonomy constants -/

def taxonomyHDF5FileCount : Nat := 243
def taxonomyEventCount : Nat := 26
def taxonomyPyringCount : Nat := 225
def taxonomyPSEOBNRv4HMCount : Nat := 18
def taxonomyKerrCount : Nat := 159
def taxonomyMMRDNPCount : Nat := 44
def taxonomyDampedSinusoidCount : Nat := 22
def taxonomyWaveformCount : Nat := 18
def taxonomyTotalCompressedSize : Nat := 1444151741
def taxonomyTotalUncompressedSize : Nat := 1963931876
def taxonomySmallestMember : String := "rin/rin_S190727h_pyring_DS_1mode_10M.h5"
def taxonomyLargestMember : String := "rin/rin_S191109d_pseobnrv4hm.h5"

/-! ## §2. Count identities -/

theorem taxonomy_pipeline_sum :
    taxonomyPyringCount + taxonomyPSEOBNRv4HMCount = taxonomyHDF5FileCount := by
  unfold taxonomyPyringCount taxonomyPSEOBNRv4HMCount taxonomyHDF5FileCount
  decide

theorem taxonomy_category_sum :
    taxonomyKerrCount + taxonomyMMRDNPCount + taxonomyDampedSinusoidCount +
      taxonomyWaveformCount = taxonomyHDF5FileCount := by
  unfold taxonomyKerrCount taxonomyMMRDNPCount taxonomyDampedSinusoidCount
    taxonomyWaveformCount taxonomyHDF5FileCount
  decide

theorem taxonomy_hdf5_count_matches_zip_schema :
    taxonomyHDF5FileCount = ringdownZipH5Count := rfl

theorem taxonomy_total_compressed_matches_zip_schema :
    taxonomyTotalCompressedSize = ringdownZipTotalCompressedSize := rfl

theorem taxonomy_total_uncompressed_matches_zip_schema :
    taxonomyTotalUncompressedSize = ringdownZipTotalUncompressedSize := rfl

theorem taxonomy_uncompressed_gt_compressed :
    taxonomyTotalCompressedSize < taxonomyTotalUncompressedSize := by
  unfold taxonomyTotalCompressedSize taxonomyTotalUncompressedSize
  decide

theorem taxonomy_event_count_pos : 0 < taxonomyEventCount := by
  unfold taxonomyEventCount
  decide

theorem taxonomy_smallest_member_named :
    taxonomySmallestMember = "rin/rin_S190727h_pyring_DS_1mode_10M.h5" := rfl

theorem taxonomy_largest_member_named :
    taxonomyLargestMember = "rin/rin_S191109d_pseobnrv4hm.h5" := rfl

/-! ## §3. Master cert -/

structure GWTC3RingdownFilenameTaxonomyCert where
  pipeline_sum : taxonomyPyringCount + taxonomyPSEOBNRv4HMCount = taxonomyHDF5FileCount
  category_sum :
    taxonomyKerrCount + taxonomyMMRDNPCount + taxonomyDampedSinusoidCount +
      taxonomyWaveformCount = taxonomyHDF5FileCount
  hdf5_count_matches_zip : taxonomyHDF5FileCount = ringdownZipH5Count
  compressed_matches_zip : taxonomyTotalCompressedSize = ringdownZipTotalCompressedSize
  uncompressed_matches_zip : taxonomyTotalUncompressedSize = ringdownZipTotalUncompressedSize
  uncompressed_gt_compressed : taxonomyTotalCompressedSize < taxonomyTotalUncompressedSize
  event_count_pos : 0 < taxonomyEventCount
  smallest_named :
    taxonomySmallestMember = "rin/rin_S190727h_pyring_DS_1mode_10M.h5"
  largest_named :
    taxonomyLargestMember = "rin/rin_S191109d_pseobnrv4hm.h5"
  zip_schema_available : Nonempty GWTC3RingdownZipSchemaCert

def gwtc3RingdownFilenameTaxonomyCert :
    GWTC3RingdownFilenameTaxonomyCert where
  pipeline_sum := taxonomy_pipeline_sum
  category_sum := taxonomy_category_sum
  hdf5_count_matches_zip := taxonomy_hdf5_count_matches_zip_schema
  compressed_matches_zip := taxonomy_total_compressed_matches_zip_schema
  uncompressed_matches_zip := taxonomy_total_uncompressed_matches_zip_schema
  uncompressed_gt_compressed := taxonomy_uncompressed_gt_compressed
  event_count_pos := taxonomy_event_count_pos
  smallest_named := taxonomy_smallest_member_named
  largest_named := taxonomy_largest_member_named
  zip_schema_available := gwtc3RingdownZipSchemaCert_inhabited

theorem gwtc3RingdownFilenameTaxonomyCert_inhabited :
    Nonempty GWTC3RingdownFilenameTaxonomyCert :=
  ⟨gwtc3RingdownFilenameTaxonomyCert⟩

/-- One-statement filename-taxonomy theorem. -/
theorem gwtc3_ringdown_filename_taxonomy_one_statement :
    (taxonomyHDF5FileCount = 243) ∧
    (taxonomyEventCount = 26) ∧
    (taxonomyPyringCount = 225) ∧
    (taxonomyPSEOBNRv4HMCount = 18) ∧
    (taxonomyKerrCount + taxonomyMMRDNPCount + taxonomyDampedSinusoidCount +
      taxonomyWaveformCount = taxonomyHDF5FileCount) ∧
    Nonempty GWTC3RingdownFilenameTaxonomyCert :=
  ⟨rfl, rfl, rfl, rfl, taxonomy_category_sum,
   gwtc3RingdownFilenameTaxonomyCert_inhabited⟩

end GWTC3RingdownFilenameTaxonomy
end Verification
end IndisputableMonolith
