import Mathlib

/-!
# GWTC-3 Posterior Manifest

## Status: STRUCTURAL THEOREM (0 sorry, 0 RS-internal axiom; closure 2026-05-22).

This module records the exact public Zenodo posterior-file manifest
needed to upgrade `GWTC3RingdownStatus` from a status record to a real
posterior likelihood artifact.

Zenodo record:

* `7007370`
* Title: `Data release for Tests of General Relativity with GWTC-3`

Required files:

* `IGWN-GWTC3-TGR-v1-rin.zip` — ringdown test posterior files.
* `IGWN-GWTC3-TGR-v1-imr.zip` — inspiral-merger-ringdown consistency.
* `IGWN-GWTC3-TGR-v1-par.zip` — parameterized GR tests.
* `IGWN-GWTC3-TGR-v1-liv.zip` — Lorentz-invariance violation.
* `IGWN-GWTC3-TGR-v1-sim.zip` — spin-induced quadrupole moment.

The Lean content is the manifest completeness and positivity theorem:
the five expected posterior files are named, have positive byte sizes,
and are tied to a single Zenodo record id. The companion reproducibility
script `papers/reproducibility/gwtc3_posterior_manifest.py` fetches the
same metadata live from the Zenodo API and writes JSON/CSV outputs.

This is **posterior-ingestion preparation**, not posterior likelihood.
Zero `sorry`. Zero new RS-specific axioms.
-/

namespace IndisputableMonolith
namespace Verification
namespace GWTC3PosteriorManifest

/-! ## §1. Manifest records -/

/-- A posterior-file manifest entry. -/
structure PosteriorFile where
  key : String
  sizeBytes : Nat
  checksum : String

def zenodoRecordId : Nat := 7007370

def imrFile : PosteriorFile where
  key := "IGWN-GWTC3-TGR-v1-imr.zip"
  sizeBytes := 4120399443
  checksum := "md5:0a89b6c3d7f43496a4a1b57bb2ac4e32"

def ringdownFile : PosteriorFile where
  key := "IGWN-GWTC3-TGR-v1-rin.zip"
  sizeBytes := 1444203951
  checksum := "md5:131d4d5e057f5e1c58787ca2920796a4"

def simFile : PosteriorFile where
  key := "IGWN-GWTC3-TGR-v1-sim.zip"
  sizeBytes := 1317455705
  checksum := "md5:fb4ed440b11caf2e0d5b2b4c8c4da707"

def livFile : PosteriorFile where
  key := "IGWN-GWTC3-TGR-v1-liv.zip"
  sizeBytes := 7404733110
  checksum := "md5:71575f4a17a5f967fa5903a1f0fbe1b1"

def parFile : PosteriorFile where
  key := "IGWN-GWTC3-TGR-v1-par.zip"
  sizeBytes := 2523809848
  checksum := "md5:9a5a1d332e7d47813a7d443e28f27396"

def allPosteriorFiles : List PosteriorFile :=
  [imrFile, ringdownFile, simFile, livFile, parFile]

/-! ## §2. Completeness and positivity -/

def HasPositiveSize (f : PosteriorFile) : Prop :=
  0 < f.sizeBytes

theorem imr_size_pos : HasPositiveSize imrFile := by
  unfold HasPositiveSize imrFile
  decide

theorem ringdown_size_pos : HasPositiveSize ringdownFile := by
  unfold HasPositiveSize ringdownFile
  decide

theorem sim_size_pos : HasPositiveSize simFile := by
  unfold HasPositiveSize simFile
  decide

theorem liv_size_pos : HasPositiveSize livFile := by
  unfold HasPositiveSize livFile
  decide

theorem par_size_pos : HasPositiveSize parFile := by
  unfold HasPositiveSize parFile
  decide

theorem posterior_manifest_has_five_files :
    allPosteriorFiles.length = 5 := by
  unfold allPosteriorFiles
  decide

theorem posterior_manifest_record_id_pos : 0 < zenodoRecordId := by
  unfold zenodoRecordId
  decide

/-- Ringdown posterior file is explicitly named in the manifest. -/
theorem ringdown_file_key :
    ringdownFile.key = "IGWN-GWTC3-TGR-v1-rin.zip" := rfl

/-! ## §3. Master cert -/

structure GWTC3PosteriorManifestCert where
  record_id_pos : 0 < zenodoRecordId
  five_files : allPosteriorFiles.length = 5
  imr_positive : HasPositiveSize imrFile
  ringdown_positive : HasPositiveSize ringdownFile
  sim_positive : HasPositiveSize simFile
  liv_positive : HasPositiveSize livFile
  par_positive : HasPositiveSize parFile
  ringdown_named : ringdownFile.key = "IGWN-GWTC3-TGR-v1-rin.zip"

def gwtc3PosteriorManifestCert : GWTC3PosteriorManifestCert where
  record_id_pos := posterior_manifest_record_id_pos
  five_files := posterior_manifest_has_five_files
  imr_positive := imr_size_pos
  ringdown_positive := ringdown_size_pos
  sim_positive := sim_size_pos
  liv_positive := liv_size_pos
  par_positive := par_size_pos
  ringdown_named := ringdown_file_key

theorem gwtc3PosteriorManifestCert_inhabited :
    Nonempty GWTC3PosteriorManifestCert :=
  ⟨gwtc3PosteriorManifestCert⟩

/-- One-statement manifest theorem: the GWTC-3 posterior manifest names
all five expected tests-of-GR zip files, including the ringdown file
required for RS echo/QNM posterior likelihood work. -/
theorem gwtc3_posterior_manifest_one_statement :
    (zenodoRecordId = 7007370) ∧
    (allPosteriorFiles.length = 5) ∧
    (ringdownFile.key = "IGWN-GWTC3-TGR-v1-rin.zip") ∧
    (HasPositiveSize imrFile) ∧
    (HasPositiveSize ringdownFile) ∧
    (HasPositiveSize simFile) ∧
    (HasPositiveSize livFile) ∧
    (HasPositiveSize parFile) ∧
    Nonempty GWTC3PosteriorManifestCert :=
  ⟨rfl,
   posterior_manifest_has_five_files,
   ringdown_file_key,
   imr_size_pos,
   ringdown_size_pos,
   sim_size_pos,
   liv_size_pos,
   par_size_pos,
   gwtc3PosteriorManifestCert_inhabited⟩

end GWTC3PosteriorManifest
end Verification
end IndisputableMonolith
