.PHONY: all check coverage openscop cases validator clean

all: coverage openscop cases validator

check:
	python3 -m py_compile \
		tools/openscop_storage_diff.py \
		tools/toy_openscop_layout_remap.py \
		tools/toy_openscop_scratchpad.py \
		tools/toy_openscop_reuse_folding.py \
		tools/toy_openscop_advanced_storage.py \
		tools/toy_openscop_private_protocols.py \
		tools/toy_openscop_boundary_domain.py \
		tools/summarize_standalone.py \
		tools/build_manifest.py \
		tools/build_example_catalog.py \
		tools/build_case_folders.py
	rm -rf tools/__pycache__

coverage: check
	python3 tools/summarize_standalone.py \
		evidence/standalone_positive.log \
		evidence/standalone_negative.log \
		> evidence/standalone_coverage.md
	python3 tools/summarize_standalone.py \
		evidence/standalone_positive.log \
		evidence/standalone_negative.log \
		--format json \
		> evidence/standalone_coverage.json
	python3 tools/build_manifest.py \
		--positive evidence/standalone_positive.log \
		--negative evidence/standalone_negative.log \
		--examples examples/standalone \
		--format markdown \
		> MANIFEST.md
	python3 tools/build_manifest.py \
		--positive evidence/standalone_positive.log \
		--negative evidence/standalone_negative.log \
		--examples examples/standalone \
		--format json \
		> MANIFEST.json
	python3 tools/build_example_catalog.py \
		--positive evidence/standalone_positive.log \
		--negative evidence/standalone_negative.log \
		--examples examples/standalone \
		--format markdown \
		> EXAMPLE_CATALOG.md
	python3 tools/build_example_catalog.py \
		--positive evidence/standalone_positive.log \
		--negative evidence/standalone_negative.log \
		--examples examples/standalone \
		--format json \
		> EXAMPLE_CATALOG.json

openscop: check
	python3 tools/openscop_storage_diff.py \
		evidence/candl_scalexp0.scop \
		evidence/candl_scalexp1.scop \
		> evidence/candl_scalexp_summary.txt
	python3 tools/openscop_storage_diff.py \
		evidence/candl_scalpriv0.scop \
		evidence/candl_scalpriv1.scop \
		> evidence/candl_scalpriv_summary.txt
	python3 tools/toy_openscop_layout_remap.py \
		evidence/candl_scalexp0.scop \
		evidence/toy_layout_remap_a_scale2.scop \
		--array a --scale 2
	python3 tools/openscop_storage_diff.py \
		evidence/candl_scalexp0.scop \
		evidence/toy_layout_remap_a_scale2.scop \
		> evidence/toy_layout_remap_summary.txt
	python3 tools/toy_openscop_scratchpad.py \
		--out-dir evidence
	python3 tools/openscop_storage_diff.py \
		evidence/toy_scratchpad_packing_source.scop \
		evidence/toy_scratchpad_packing_target.scop \
		> evidence/toy_scratchpad_packing_summary.txt
	python3 tools/openscop_storage_diff.py \
		evidence/toy_scratchpad_copyout_source.scop \
		evidence/toy_scratchpad_copyout_target.scop \
		> evidence/toy_scratchpad_copyout_summary.txt
	python3 tools/toy_openscop_reuse_folding.py \
		--out-dir evidence
	python3 tools/openscop_storage_diff.py \
		evidence/toy_array_contraction_source.scop \
		evidence/toy_array_contraction_target.scop \
		> evidence/toy_array_contraction_summary.txt
	python3 tools/openscop_storage_diff.py \
		evidence/toy_inter_array_reuse_source.scop \
		evidence/toy_inter_array_reuse_target.scop \
		> evidence/toy_inter_array_reuse_summary.txt
	python3 tools/openscop_storage_diff.py \
		evidence/toy_double_buffering_source.scop \
		evidence/toy_double_buffering_target.scop \
		> evidence/toy_double_buffering_summary.txt
	python3 tools/toy_openscop_advanced_storage.py \
		--out-dir evidence
	python3 tools/openscop_storage_diff.py \
		evidence/toy_versioning_source.scop \
		evidence/toy_versioning_target.scop \
		> evidence/toy_versioning_summary.txt
	python3 tools/openscop_storage_diff.py \
		evidence/toy_reduction_source.scop \
		evidence/toy_reduction_target.scop \
		> evidence/toy_reduction_summary.txt
	python3 tools/openscop_storage_diff.py \
		evidence/toy_overlap_source.scop \
		evidence/toy_overlap_target.scop \
		> evidence/toy_overlap_summary.txt
	python3 tools/openscop_storage_diff.py \
		evidence/toy_view_composition_source.scop \
		evidence/toy_view_composition_target.scop \
		> evidence/toy_view_composition_summary.txt
	python3 tools/toy_openscop_private_protocols.py \
		--out-dir evidence
	python3 tools/openscop_storage_diff.py \
		evidence/toy_private_copy_boundary_source.scop \
		evidence/toy_private_copy_boundary_target.scop \
		> evidence/toy_private_copy_boundary_summary.txt
	python3 tools/openscop_storage_diff.py \
		evidence/toy_private_access_source.scop \
		evidence/toy_private_access_target.scop \
		> evidence/toy_private_access_summary.txt
	python3 tools/openscop_storage_diff.py \
		evidence/toy_scalar_promotion_source.scop \
		evidence/toy_scalar_promotion_target.scop \
		> evidence/toy_scalar_promotion_summary.txt
	python3 tools/toy_openscop_boundary_domain.py \
		--out-dir evidence
	python3 tools/openscop_storage_diff.py \
		evidence/toy_no_alias_source.scop \
		evidence/toy_no_alias_target.scop \
		> evidence/toy_no_alias_summary.txt
	python3 tools/openscop_storage_diff.py \
		evidence/toy_frame_source.scop \
		evidence/toy_frame_target.scop \
		> evidence/toy_frame_summary.txt
	python3 tools/openscop_storage_diff.py \
		evidence/toy_index_split_source.scop \
		evidence/toy_index_split_target.scop \
		> evidence/toy_index_split_summary.txt

cases: coverage
	python3 tools/build_case_folders.py \
		--catalog EXAMPLE_CATALOG.json \
		--manifest MANIFEST.json \
		--out-dir cases

validator: cases
	mkdir -p validator/_build
	ocamlc -o validator/_build/storage_validator validator/storage_validator.ml
	./validator/_build/storage_validator cases

clean:
	rm -rf tools/__pycache__
	rm -rf validator/_build
	rm -f validator/*.cmi validator/*.cmo
