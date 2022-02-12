# Changelog (unreleased)

## [Unreleased]

### Added

- in `ereal.v`:
  + lemmas `esum_ninftyP`, `esum_pinftyP`
  + lemmas `addeoo`, `daddeoo`
  + lemmas `desum_pinftyP`, `desum_ninftyP`
- in `topology.v`:
  + definitions `compact_near`, `precompact`, `locally_compact`
  + lemmas `precompactE`, `precompact_subset`, `compact_precompact`, 
      `precompact_closed`
  + definitions `equicontinuous`, `pointwise_precompact`
  + lemmas `equicontinuous_subset`, `equicontinuous_cts`
  + lemmas `pointwise_precomact_subset`, `pointwise_precompact_precompact`
      `uniform_pointwise_compact`, `compact_pointwise_precompact`

### Changed

- in `trigo.v`:
  + the `realType` argument of `pi` is implicit
  + the printed type of `acos`, `asin`, `atan` is `R -> R`

### Renamed

### Removed

- in `ereal.v`:
  + lemmas `esum_fset_ninfty`, `esum_fset_pinfty`
  + lemmas `desum_fset_pinfty`, `desum_fset_ninfty`

### Infrastructure

### Misc
